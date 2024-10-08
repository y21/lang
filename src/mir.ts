import { bug, spanless_bug } from "./error";
import { FnDecl, ExternFnDecl, RecordFields, BinaryOp, UnaryOp, LetDecl, FnParameter, Stmt, Expr, AstEnum, VariantId, Impl, AstFnSignature, Trait } from "./parse";
import { BindingPat, Resolutions, TraitFn, TypeResolution } from "./resolve";
import { joinSpan } from "./span";
import { TokenType } from "./token";
import { IntTy, Ty, instantiateTy, isUnit, BOOL, U8, eqTy, TyParamCheck } from "./ty";
import { exprTy as rawExprTyCoerced, InstantiatedFnSig, TypeckResults } from "./typeck";
import { assertUnreachable, assert, todo } from "./util";

export type MirValue = { type: 'int', ity: IntTy, value: number }
    | { type: 'bool', value: boolean }
    | { type: 'str', value: string }
    | { type: 'Local', value: MirLocalId<true> }
    | { type: 'Unreachable' }
    | { type: 'FnDef', value: FnDecl }
    | { type: 'TraitFn', value: FnDecl }
    | { type: 'ExternFnDef', value: ExternFnDecl }
    | { type: 'Record', value: RecordFields<MirValue> }
    | { type: 'Tuple', value: MirValue[] }
    | { type: 'Variant', enum: AstEnum, variant: VariantId };

export const UNIT_MIR: MirValue = { type: 'Tuple', value: [] };

/**
 * `temporary` indicates whether this local is used for a subexpression.
 * These are trivially in SSA form and are never written to except when initialized.
 */
export type MirLocal<temporary extends boolean = boolean> = { ty: Ty, temporary: temporary };
export type MirLocalId<temporary extends boolean = boolean> = number;
export type Projection = { type: 'Field', property: string | number } | { type: 'Index', index: MirValue } | { type: 'Deref' };
export type MirPlace<temporary extends boolean = boolean> = { base: MirLocalId<temporary>, projections: Projection[] };
export type MirBinOp = Exclude<BinaryOp, TokenType.AndAnd | TokenType.OrOr>;
export type MirStmt = { type: 'Assignment', assignee: MirPlace, value: MirValue }
    | { type: 'BinOp', op: MirBinOp, assignee: MirLocalId<true>, lhs: MirValue, lhsTy: Ty, rhs: MirValue }
    | { type: 'Unary', op: UnaryOp, assignee: MirLocalId<true>, rhs: MirValue }
    | { type: 'Copy', assignee: MirLocalId<true>, place: MirPlace }
    | { type: 'AddrOf', assignee: MirLocalId<true>, place: MirPlace }
    | { type: 'Bitcast', from_ty: Ty, to_ty: Ty, assignee: MirLocalId<true>, value: MirValue }
    | { type: 'Ext', from_ty: Ty, to_ty: Ty, assignee: MirLocalId<true>, value: MirValue }
    | { type: 'Trunc', from_ty: Ty, to_ty: Ty, assignee: MirLocalId<true>, value: MirValue }
    | { type: 'InitArrayLit', assignee: MirLocalId<true>, ty: { type: 'Array' } & Ty, values: MirValue[] }
    | { type: 'InitArrayRepeat', assignee: MirLocalId<true>, ty: { type: 'Array' } & Ty, value: MirValue, count: number }
    | { type: 'StrStartsWith', assignee: MirLocalId<true>, lhs: MirValue, rhs: MirValue }
    // Go from T[n]* to T[]*
    | { type: 'UnsizeArray', assignee: MirLocalId<true>, base: MirValue, len: number, slicePtrTy: Ty & { type: 'Pointer' } };
export type MirTerminator = { type: 'Return' }
    | { type: 'Call', assignee: MirLocalId<true>, args: MirValue[], decl: FnDecl | ExternFnDecl, sig: InstantiatedFnSig, target: MirBlockId }
    | { type: 'Conditional', condition: MirValue, then: MirBlockId, else: MirBlockId }
    | { type: 'Jump', target: MirBlockId };
export type MirBlock = {
    stmts: MirStmt[];
    terminator: MirTerminator | null;
};
export type MirBlockId = number;
export type MirBody = { blocks: MirBlock[], parameters: MirLocalId<false>[], locals: MirLocal[] };

type BreakableInfo = {
    breakTarget: MirBlockId,
    continueTarget: MirBlockId
};

const _mirBodyCache = new Map<string, MirBody>();

/**
 * Instantiates a function's MIR with the given generic arguments.
 * 
 *    fn f<T>(v: T) {}
 * 
 * calling `astToMir(f, [i32])` will create the MIR body for `function f(v: i32)`, and cache it.
 */
export function astToMir(src: string, mangledName: string, decl: FnDecl, args: Ty[], resolutions: Resolutions, typeck: TypeckResults): MirBody {
    const exprTyCoercions = (expr: Expr) => rawExprTyCoerced(typeck, expr);
    const exprTyNoCoercions = (expr: Expr) => typeck.exprTys.get(expr) || bug(expr.span, 'expr does not have a registered type');

    function lowerMir(): MirBody {
        if (decl.body.type !== 'Block') bug(decl.body.span, `${decl.sig.name} did not have a block as its body?`);

        const astLocalToMirLocal = new Map<LetDecl | FnParameter | BindingPat, MirLocalId<false>>();
        const breakableInfo = new Map<{ type: 'While' } & Expr, BreakableInfo>();
        const locals: MirLocal[] = [];
        const addLocal = <temporary extends boolean = boolean>(ty: Ty, temporary: temporary): MirLocalId<temporary> => {
            ty = instantiateTy(ty, args);
            locals.push({ ty, temporary });
            return locals.length - 1;
        };
        const addBlock = (): MirBlockId => {
            blocks.push({ stmts: [], terminator: null });
            return blocks.length - 1;
        };
        const retTy = decl.sig.ret && typeck.loweredTys.get(decl.sig.ret)!;
        const hasSignificantReturn = retTy && !isUnit(retTy);
        if (hasSignificantReturn) {
            // _0 = return place
            assert(addLocal(retTy, false) === 0);
        }
        const returnPlace = locals[0] as MirLocal<false>;
        const returnId = 0 as MirLocalId<false>;
        const blocks: MirBlock[] = [
            {
                stmts: [],
                terminator: null,
            }
        ];
        let block = blocks[0];

        const mkBinOp = (lhs: MirValue, rhs: MirValue, op: MirBinOp, lhsTy: Ty): { type: 'Local' } & MirValue => {
            const binOpRes = addLocal(BOOL, true);
            block.stmts.push({
                type: 'BinOp',
                assignee: binOpRes,
                lhs,
                rhs,
                lhsTy,
                op
            });
            return { type: 'Local', value: binOpRes };
        }

        const parameters = [];
        for (const param of decl.sig.parameters) {
            let ty: Ty;
            if (param.type === 'Receiver') {
                ty = typeck.loweredTys.get((decl.parent as Impl).selfTy)!;
                if (param.ptr) {
                    ty = { type: 'Pointer', flags: ty.flags, mtb: param.ptr, pointee: ty };
                }
            } else {
                ty = typeck.loweredTys.get(param.ty)!;
            }
            const local = addLocal(ty, false);
            parameters.push(local);
            astLocalToMirLocal.set(param, local);
        }

        /**
         * If the given value is a place, assigns a copy of it to a local and returns that local.
         * Otherwise returns the value unchanged.
         */
        function asValue(val: ({ type: 'Place' } & MirPlace<boolean>) | MirValue, ty: Ty): MirValue {
            if (val.type === 'Place') {
                const res = addLocal(ty, true);
                block.stmts.push({
                    type: 'Copy',
                    assignee: res,
                    place: val
                });
                return { type: 'Local', value: res };
            } else {
                return val;
            }
        }
        function requireAsPlace(val: ({ type: 'Place' } & MirPlace<boolean>) | MirValue): { type: 'Place' } & MirPlace<boolean> {
            let place = val.type === 'Local'
                ? { type: 'Place', base: val.value, projections: [] } as ({ type: 'Place' } & MirPlace<boolean>)
                : val;

            if (place.type === 'Place') {
                return place;
            } else {
                spanless_bug(`place was expected, got ${place.type}`);
            }
        }

        function lowerStmt(stmt: Stmt) {
            switch (stmt.type) {
                case 'Impl': break;
                case 'FnDecl': break; // Nested bodies are only lowered when explicitly requested
                case 'Mod':
                case 'Trait': break;
                case 'ExternFnDecl':
                    // Extern fns don't have a body, nothing needs to be lowered
                    // TODO: we might want to at the very least validate intrinsic signatures
                    break;
                case 'LetDecl': {
                    const ty = typeck.patTys.get(stmt)!;
                    const local = addLocal(ty, false);
                    astLocalToMirLocal.set(stmt, local);
                    if (stmt.init) {
                        const value = asValue(lowerExpr(stmt.init), ty);
                        block.stmts.push({ type: 'Assignment', assignee: { base: local, projections: [] }, value });
                    }
                    break;
                }
                case 'Expr': lowerExpr(stmt.value); break;
                case 'TyAlias':
                case 'Use': break;
                default: assertUnreachable(stmt);
            }
        }

        function lowerReturnValue(value: MirValue): MirValue {
            if (hasSignificantReturn) {
                block.stmts.push({ type: 'Assignment', assignee: { base: returnId, projections: [] }, value });
                block.terminator = { type: 'Return' };
            } else {
                block.terminator = { type: 'Return' };
            }
            let newBlock = { stmts: [], terminator: null };
            blocks.push(newBlock);
            block = newBlock;
            return { type: 'Unreachable' };
        }

        function instantiateFnSig(sig: InstantiatedFnSig, args: Ty[]): InstantiatedFnSig {
            return {
                args: sig.args.map(ty => instantiateTy(ty, args)),
                parameters: sig.parameters.map(ty => instantiateTy(ty, args)),
                ret: instantiateTy(sig.ret, args)
            }
        }

        type LowerExprResult = MirValue | ({ type: 'Place' } & MirPlace);

        function lowerExprInner(expr: Expr): LowerExprResult {
            switch (expr.type) {
                case 'Number': {
                    const ity = exprTyNoCoercions(expr);
                    if (ity.type !== 'int') {
                        bug(expr.span, 'number expression was not an int type');
                    }
                    return { type: 'int', ity: ity.value, value: expr.value };
                }
                case 'ByteCharacter': return { type: 'int', ity: U8.value, value: expr.value.charCodeAt(0) };
                case 'String': return { type: 'str', value: expr.value };
                case 'Path': {
                    const resolution = resolutions.valueResolutions.get(expr)!;
                    switch (resolution.type) {
                        case 'FnParam':
                        case 'LetDecl':
                        case 'Binding': {
                            let id: MirLocalId;
                            switch (resolution.type) {
                                case 'FnParam': id = astLocalToMirLocal.get(resolution.param)!; break;
                                case 'LetDecl':
                                case "Binding": id = astLocalToMirLocal.get(resolution)!;
                            }
                            return { type: 'Place', base: id, projections: [] };
                        }
                        case 'ExternFnDecl': return { type: 'ExternFnDef', value: resolution };
                        case 'Variant': return { type: 'Variant', enum: resolution.enum, variant: resolution.variant };
                        case 'TypeRelative':
                        case 'FnDecl':
                        case 'TraitFn': {
                            const ty = typeck.exprTys.get(expr)!;
                            if (ty.type === 'FnDef') {
                                return { type: 'FnDef', value: ty.decl };
                            } else if (ty.type === 'TraitFn') {
                                const selfTy = instantiateTy(ty.args[0], args);
                                for (const [implSelfTy, impl] of typeck.impls) {
                                    if (impl.ofTrait) {
                                        const trait = resolutions.tyResolutions.get(impl.ofTrait!) as Trait;

                                        if (eqTy(selfTy, implSelfTy, TyParamCheck.Unreachable) && trait === ty.value.parentTrait) {
                                            const item = impl.items.find(i => i.decl.sig.name === ty.value.sig.name);
                                            if (item) {
                                                return { type: 'TraitFn', value: item.decl };
                                            }
                                        }
                                    }
                                }

                                bug(expr.span, 'failed to find impl for trait fn call');
                            } else {
                                bug(expr.span, 'call target has invalid type: ' + ty);
                            }
                        }
                        default: assertUnreachable(resolution);
                    }
                }
                case 'Return': {
                    const ret = asValue(lowerExpr(expr.value), exprTyNoCoercions(expr.value));
                    return lowerReturnValue(ret);
                }
                case 'Binary': {
                    const lhsTy = exprTyNoCoercions(expr.lhs);
                    const lhs = asValue(lowerExpr(expr.lhs), lhsTy);
                    const rhs = asValue(lowerExpr(expr.rhs), exprTyNoCoercions(expr.rhs));
                    switch (expr.op) {
                        case TokenType.AndAnd:
                        case TokenType.OrOr: {
                            const res = addLocal(BOOL, false);
                            const resPlace: MirPlace = { base: res, projections: [] };
                            // TODO: simplify simple v && x with no side effects as v & x
                            // TODO 2: do we want a phi instruction in the mir to help LLVM? it can be used here

                            // lhs && rhs:
                            //
                            // br i1 _lhs, label %rhs, label %lhs.false
                            //
                            // rhs:
                            // _res = _rhs
                            // br label %join
                            //
                            // lhs.false:
                            // _res = false
                            // br label %join

                            // lhs || rhs
                            // br i1 _lhs, label %lhs.true, label %rhs

                            const lhsBlock = addBlock();
                            const rhsBlock = addBlock();
                            const joinBlock = addBlock();

                            block.terminator = {
                                type: 'Conditional',
                                condition: lhs,
                                then: expr.op === TokenType.AndAnd ? rhsBlock : lhsBlock,
                                else: expr.op === TokenType.AndAnd ? lhsBlock : rhsBlock,
                            };

                            block = blocks[rhsBlock];
                            block.stmts.push({
                                type: 'Assignment',
                                assignee: resPlace,
                                value: rhs
                            });
                            block.terminator = { type: 'Jump', target: joinBlock };

                            block = blocks[lhsBlock];
                            block.stmts.push({
                                type: 'Assignment',
                                assignee: resPlace,
                                value: { type: 'bool', value: expr.op !== TokenType.AndAnd }
                            });
                            block.terminator = { type: 'Jump', target: joinBlock };

                            block = blocks[joinBlock];
                            const copyRes = addLocal(BOOL, true);
                            block.stmts.push({
                                type: 'Copy',
                                place: resPlace,
                                assignee: copyRes
                            });
                            return { type: 'Local', value: copyRes };
                        }
                        default: {
                            const res = addLocal(exprTyNoCoercions(expr), true);
                            block.stmts.push({ type: 'BinOp', assignee: res, lhs, lhsTy, rhs, op: expr.op });
                            return { type: 'Local', value: res };
                        }
                    }
                }
                case 'Unary': {
                    const rhs = asValue(lowerExpr(expr.rhs), exprTyNoCoercions(expr.rhs));
                    const res = addLocal(exprTyNoCoercions(expr), true);
                    block.stmts.push({ type: 'Unary', assignee: res, rhs, op: expr.op });
                    return { type: 'Local', value: res };
                }
                case 'AddrOf': {
                    const pointee = requireAsPlace(lowerExpr(expr.pointee));
                    const res = addLocal(exprTyNoCoercions(expr), true);
                    block.stmts.push({ type: 'AddrOf', assignee: res, place: pointee });
                    return { type: 'Local', value: res };
                }
                case 'Assignment': {
                    switch (expr.op) {
                        case TokenType.Assign: {
                            let assignee = requireAsPlace(lowerExpr(expr.target));

                            const value = asValue(lowerExpr(expr.value), exprTyNoCoercions(expr.value));
                            block.stmts.push({
                                type: 'Assignment',
                                assignee,
                                value
                            });
                            break;
                        }
                        case TokenType.AddAssign:
                        case TokenType.SubAssign:
                        case TokenType.MulAssign:
                        case TokenType.DivAssign:
                        case TokenType.RemAssign: {
                            // Lower `*x() += 2` to:
                            //   _place = x()
                            //   _val = *_place
                            //   _res = _val + 2
                            //   *_place = _res
                            const rhsTy = exprTyNoCoercions(expr.value);
                            const val = asValue(lowerExpr(expr.value), rhsTy);
                            const target = lowerExpr(expr.target);
                            const targetPlace = requireAsPlace(target);
                            const targetVal = asValue(target, exprTyNoCoercions(expr.target));
                            const binOpRes = addLocal(rhsTy, true);

                            let op: BinaryOp;
                            switch (expr.op) {
                                case TokenType.AddAssign: op = TokenType.Plus; break;
                                case TokenType.SubAssign: op = TokenType.Minus; break;
                                case TokenType.MulAssign: op = TokenType.Star; break;
                                case TokenType.DivAssign: op = TokenType.Slash; break;
                                case TokenType.RemAssign: op = TokenType.Percent; break;
                            }

                            block.stmts.push({
                                assignee: binOpRes,
                                type: 'BinOp',
                                op,
                                lhs: targetVal,
                                lhsTy: rhsTy,
                                rhs: val
                            });

                            block.stmts.push({
                                type: 'Assignment',
                                assignee: targetPlace,
                                value: { type: 'Local', value: binOpRes }
                            });
                            break;
                        }
                        default: assertUnreachable(expr);
                    }
                    return UNIT_MIR;
                }
                case 'Deref': {
                    let pointee = requireAsPlace(lowerExpr(expr.pointee));
                    pointee.projections.push({ type: 'Deref' });
                    return pointee;
                }
                case 'FnCall': {
                    const sig = instantiateFnSig(typeck.instantiatedFnSigs.get(expr)!, args);

                    // calls to intrinsics are special cased
                    if (expr.callee.type === 'Path') {
                        const res = resolutions.valueResolutions.get(expr.callee)!;
                        if (res.type === 'ExternFnDecl' && res.abi === 'intrinsic') {
                            const transmutableIntrinsic = (type: 'Bitcast' | 'Ext' | 'Trunc'): LowerExprResult => {
                                const fromTy = instantiateTy(sig.parameters[0], args);
                                const toTy = instantiateTy(sig.ret, args);
                                const assignee = addLocal(toTy, true);
                                const value = asValue(lowerExpr(expr.args[0]), fromTy);

                                block.stmts.push({ type, assignee, from_ty: fromTy, to_ty: toTy, value });
                                return { type: 'Local', value: assignee };
                            }

                            switch (res.sig.name) {
                                case 'bitcast': return transmutableIntrinsic('Bitcast');
                                case 'ext': return transmutableIntrinsic('Ext');
                                case 'trunc': return transmutableIntrinsic('Trunc');
                                default: bug(expr.span, `unknown intrinsic: ${res.sig.name}`);
                            }
                        }
                    }

                    const callee = lowerExpr(expr.callee);
                    let decl: FnDecl | ExternFnDecl | null = null;

                    if (callee.type === 'FnDef' || callee.type === 'ExternFnDef') {
                        decl = callee.value;
                    } else if (callee.type === 'TraitFn') {
                        decl = callee.value;
                    } else {
                        bug(expr.span, `unknown callee type: ${callee.type}`);
                    }
                    const res = addLocal(sig.ret, true);

                    const callArgs = expr.args.map(v => asValue(lowerExpr(v), exprTyNoCoercions(v)));

                    const targetBlock = blocks.length;
                    blocks.push({ stmts: [], terminator: null });

                    block.terminator = { type: 'Call', args: callArgs, assignee: res, decl: decl!, sig, target: targetBlock };
                    block = blocks[targetBlock];

                    return { type: 'Local', value: res };
                }
                case 'Property': {
                    const val = requireAsPlace(lowerExpr(expr.target));
                    if (expr.deref) {
                        val.projections.push({ type: 'Deref' });
                    }
                    val.projections.push({ type: 'Field', property: expr.property });
                    return val;
                }
                case 'Index': {
                    const target = requireAsPlace(lowerExpr(expr.target));
                    const index = asValue(lowerExpr(expr.index), exprTyNoCoercions(expr.index));
                    target.projections.push({ type: 'Index', index });
                    return target;
                }
                case 'ArrayLiteral':
                case 'ArrayRepeat': {
                    const ty = exprTyNoCoercions(expr);
                    if (ty.type !== 'Array') {
                        bug(expr.span, 'array literal did not produce array type');
                    }

                    const assignee = addLocal(ty, true);
                    if (expr.type === 'ArrayLiteral') {
                        block.stmts.push({
                            assignee,
                            type: 'InitArrayLit',
                            ty,
                            values: expr.elements.map(e => asValue(lowerExpr(e), exprTyNoCoercions(e)))
                        });
                    } else {
                        block.stmts.push({
                            assignee,
                            type: 'InitArrayRepeat',
                            ty,
                            count: expr.count,
                            value: asValue(lowerExpr(expr.element), exprTyNoCoercions(expr.element))
                        });
                    }
                    return { type: 'Local', value: assignee };
                }
                case 'Record': {
                    const fields: RecordFields<MirValue> = expr.fields.map(([key, expr]) => {
                        return [key, asValue(lowerExpr(expr), exprTyNoCoercions(expr))];
                    });
                    return {
                        type: 'Record',
                        value: fields
                    }
                }
                case 'Bool': return { type: 'bool', value: expr.value };
                case 'If': {
                    const condition = asValue(lowerExpr(expr.condition), BOOL);
                    const thenBlock = addBlock();
                    const elseBlock = expr.else ? addBlock() : null;
                    const joinedBlock = addBlock();
                    const ty = exprTyNoCoercions(expr);
                    const res: MirPlace | null = expr.then.tailExpr ? { base: addLocal(ty, false), projections: [] } : null;
                    block.terminator = { type: 'Conditional', then: thenBlock, else: elseBlock ?? joinedBlock, condition };

                    block = blocks[thenBlock];
                    const thenVal = asValue(lowerExpr(expr.then), ty);
                    if (res) {
                        block.stmts.push({
                            type: 'Assignment',
                            assignee: res,
                            value: thenVal
                        });
                    }
                    block.terminator = { type: 'Jump', target: joinedBlock };

                    if (expr.else && elseBlock !== null) {
                        block = blocks[elseBlock];
                        const elseVal = asValue(lowerExpr(expr.else), ty);
                        if (res) {
                            block.stmts.push({
                                type: 'Assignment',
                                assignee: res,
                                value: elseVal
                            });
                        }
                        block.terminator = { type: 'Jump', target: joinedBlock };
                    }

                    block = blocks[joinedBlock];
                    if (res) {
                        const copyRes = addLocal(ty, true);
                        block.stmts.push({
                            type: 'Copy',
                            assignee: copyRes,
                            place: res
                        });
                        return { type: 'Local', value: copyRes };
                    } else {
                        return UNIT_MIR;
                    }
                }
                case 'While':
                    const conditionBlock = addBlock();
                    const bodyBlock = addBlock();
                    const joinedBlock = addBlock();
                    breakableInfo.set(expr, { breakTarget: joinedBlock, continueTarget: conditionBlock });
                    block.terminator = { type: 'Jump', target: conditionBlock };
                    block = blocks[conditionBlock];

                    const condition = asValue(lowerExpr(expr.condition), BOOL);
                    block.terminator = { type: 'Conditional', condition, then: bodyBlock, else: joinedBlock };

                    block = blocks[bodyBlock];
                    lowerExpr(expr.body);
                    block.terminator = { type: 'Jump', target: conditionBlock };

                    block = blocks[joinedBlock];
                    return UNIT_MIR;
                case 'Block': {
                    for (const stmt of expr.stmts) {
                        lowerStmt(stmt);
                    }
                    if (expr.tailExpr) {
                        return lowerExpr(expr.tailExpr);
                    } else {
                        return UNIT_MIR;
                    }
                }
                case 'Tuple': {
                    const elements: MirValue[] = expr.elements.map(expr => {
                        return asValue(lowerExpr(expr), exprTyNoCoercions(expr));
                    });
                    return { type: 'Tuple', value: elements };
                }
                case 'Break': {
                    const { breakTarget } = breakableInfo.get(resolutions.breakableResolutions.get(expr)!.target)!;
                    block.terminator = {
                        type: 'Jump',
                        target: breakTarget
                    };
                    const next = addBlock();
                    block = blocks[next];
                    return { type: 'Unreachable' };
                }
                case 'Continue': {
                    const { continueTarget } = breakableInfo.get(resolutions.breakableResolutions.get(expr)!.target)!;
                    block.terminator = {
                        type: 'Jump',
                        target: continueTarget
                    };
                    const next = addBlock();
                    block = blocks[next];
                    return { type: 'Unreachable' };
                }
                case 'Match': {
                    // For now, simply compile the match to a series of if-else-if, with the binding pattern acting as 'else'
                    //
                    //     let v = Enum::Variant1;
                    //     match v {
                    //         Enum::Variant1 => {}
                    //         Enum::Variant2 => {}
                    //         other => {}
                    //     }
                    //
                    // _scrutinee = Enum::Variant1
                    // br arm1
                    //
                    // arm1.check:
                    // _patternMatches = eq DiscriminantOf(_scrutinee), DiscriminantOf(Enum::Variant1)
                    // br i1 arm1.body, arm2.check
                    //
                    // arm2.check:
                    // _patternMatches = ...
                    // br i1 arm2.body, else.body
                    // 
                    // arm1.body:
                    // ...
                    // br join
                    //
                    // else.body:
                    // other = _scrutinee
                    // ...
                    // br join
                    // join:
                    // ; continue normal

                    // In check branches, we only have the pattern matching code and a branch to either the n+1 check branch or the body of this arm.
                    // Note that there will always be an n+1 branch that matches. A binding pattern as the last pattern will always match.
                    const checkBranches = expr.arms.map(() => addBlock());
                    assert(checkBranches.length > 0, 'match cannot have zero arms');
                    // In body branches, we begin by extracting bindings out of patterns and then execute normal code. At the end, we always jump to a joined block.
                    const bodyBranches = expr.arms.map(() => addBlock());
                    const joinBlock = addBlock();
                    const matchTy = exprTyNoCoercions(expr);
                    const resPlace: MirPlace | null = isUnit(matchTy) ? null : { base: addLocal(matchTy, false), projections: [] };

                    const scrutinee = lowerExpr(expr.scrutinee);
                    const scrutineeTy = exprTyNoCoercions(expr.scrutinee);
                    block.terminator = {
                        type: 'Jump',
                        target: checkBranches[0]
                    };

                    for (let i = 0; i < checkBranches.length; i++) {
                        const checkBranch = checkBranches[i];
                        const bodyBranch = bodyBranches[i];
                        const arm = expr.arms[i];

                        // Compile the check branch
                        block = blocks[checkBranch];

                        const nextCheckBlock = () => {
                            if (i === checkBranches.length - 1) {
                                // A fallible pattern cannot be the last arm (currently; until we have exhaustive checking)
                                bug(joinSpan(arm.pat.span, arm.body.span), `no check block to jump to if this arm fails`);
                            }
                            return checkBranches[i + 1];
                        }

                        const mkScrutineeBinOp = (rhs: MirValue) => {
                            const binOpRes = mkBinOp(asValue(scrutinee, scrutineeTy), rhs, TokenType.EqEq, scrutineeTy)
                            block.terminator = { type: 'Conditional', condition: { type: 'Local', value: binOpRes.value }, then: bodyBranch, else: nextCheckBlock() };
                        };

                        switch (arm.pat.type) {
                            case 'Number': {
                                if (scrutineeTy.type !== 'int') {
                                    bug(arm.pat.span, 'scrutinee is not an integer');
                                }
                                mkScrutineeBinOp({ type: 'int', ity: scrutineeTy.value, value: arm.pat.value });
                                break;
                            }
                            case 'RangeFrom': {
                                const from = arm.pat.from;
                                if (from.type !== 'String') {
                                    todo('lower ' + from.type);
                                }

                                const startsWithRes = addLocal(BOOL, true);
                                block.stmts.push({
                                    type: 'StrStartsWith',
                                    lhs: asValue(scrutinee, scrutineeTy),
                                    assignee: startsWithRes,
                                    rhs: { type: 'str', value: from.value }
                                });

                                block.terminator = { type: 'Conditional', condition: { type: 'Local', value: startsWithRes }, then: bodyBranch, else: nextCheckBlock() };
                                break;
                            }
                            case 'Path': {
                                const res = resolutions.patResolutions.get(arm.pat)!;
                                switch (res.type) {
                                    case 'Binding':
                                        // Nothing to check
                                        block.terminator = { type: 'Jump', target: bodyBranch };
                                        break;
                                    case 'Variant': {
                                        mkScrutineeBinOp({ type: 'Variant', enum: res.enum, variant: res.variant });
                                        break;
                                    }
                                }
                                break;
                            }
                            default: todo(arm.pat.type)
                        }

                        // Compile the body branch
                        block = blocks[bodyBranch];
                        switch (arm.pat.type) {
                            case 'Path': {
                                const pathres = resolutions.patResolutions.get(arm.pat)!;
                                if (pathres.type === 'Binding') {
                                    const local = addLocal(scrutineeTy, false);
                                    astLocalToMirLocal.set(pathres, local);
                                    block.stmts.push({
                                        type: 'Assignment',
                                        assignee: { base: local, projections: [] },
                                        value: asValue(scrutinee, scrutineeTy),
                                    });
                                }
                                break;
                            }
                        }
                        const bodyValue = asValue(lowerExpr(arm.body), exprTyNoCoercions(arm.body));
                        if (resPlace) {
                            block.stmts.push({
                                type: 'Assignment',
                                assignee: resPlace,
                                value: bodyValue
                            });
                        }
                        block.terminator = { type: 'Jump', target: joinBlock };
                    }

                    block = blocks[joinBlock];

                    if (resPlace) {
                        const copyRes = addLocal(matchTy, true);
                        block.stmts.push({
                            type: 'Copy',
                            assignee: copyRes,
                            place: resPlace
                        });
                        return { type: 'Local', value: copyRes };
                    } else {
                        return UNIT_MIR;
                    }
                }
                case 'MethodCall': {
                    const sig = instantiateFnSig(typeck.instantiatedFnSigs.get(expr)!, args);

                    let receiver: MirValue;
                    if (expr.deref) {
                        const recvPlace = requireAsPlace(lowerExpr(expr.target));
                        recvPlace.projections.push({ type: 'Deref' });
                        const ptrTy = exprTyNoCoercions(expr.target);
                        if (ptrTy.type !== 'Pointer') {
                            bug(expr.span, 'method call deref must be a pointer');
                        }
                        receiver = asValue(recvPlace, ptrTy.pointee);
                    } else {
                        receiver = asValue(lowerExpr(expr.target), exprTyNoCoercions(expr.target));
                    }
                    const method = typeck.selectedMethods.get(expr)!;

                    const res = addLocal(sig.ret, true);

                    const callArgs = [receiver, ...expr.args.map(v => asValue(lowerExpr(v), exprTyNoCoercions(v)))];

                    const targetBlock = blocks.length;
                    blocks.push({ stmts: [], terminator: null });

                    block.terminator = { type: 'Call', args: callArgs, assignee: res, decl: method.decl, sig, target: targetBlock };
                    block = blocks[targetBlock];

                    return { type: 'Local', value: res };
                }
                default: assertUnreachable(expr);
            }
        }

        // Essentially the same as lowerExprInner but also applies any coercions
        function lowerExpr(expr: Expr): LowerExprResult {
            const res = lowerExprInner(expr);

            const coercions = typeck.coercions.get(expr);
            if (coercions) {
                for (const coercion of coercions) {
                    switch (coercion.type) {
                        case 'Autoref': {
                            const place = requireAsPlace(res);
                            const borrowLocal = addLocal(coercion.to, true);
                            block.stmts.push({ type: 'AddrOf', assignee: borrowLocal, place });
                            return { type: 'Local', value: borrowLocal };
                        }
                        case 'UnsizeArray': {
                            const ty = typeck.exprTys.get(expr)!;
                            if (ty.type !== 'Pointer' || ty.pointee.type !== 'Array') {
                                spanless_bug('UnsizeArray operand must be an array pointer');
                            }
                            const coercee = asValue(res, ty);
                            const coercedLocal = addLocal(coercion.to, true);
                            block.stmts.push({ type: 'UnsizeArray', assignee: coercedLocal, base: coercee, len: ty.pointee.len, slicePtrTy: coercion.to });
                            return { type: 'Local', value: coercedLocal };
                        }
                        default: assertUnreachable(coercion);
                    }
                }
            }

            return res;
        }

        for (const stmt of decl.body.stmts) {
            lowerStmt(stmt);
        }

        if (!hasSignificantReturn) {
            // append implicit `ret void` statement for default return fns
            assert(block.terminator === null);
            lowerReturnValue(UNIT_MIR);
        }

        return {
            locals,
            blocks,
            parameters,
        };
    }

    let mir = _mirBodyCache.get(mangledName);
    if (!mir) {
        mir = lowerMir();
        _mirBodyCache.set(mangledName, mir);
    }
    return mir;
}
