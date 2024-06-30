import { FnDecl, ExternFnDecl, RecordFields, BinaryOp, UnaryOp, LetDecl, FnParameter, Stmt, Expr, AstEnum, VariantId } from "./parse";
import { Resolutions } from "./resolve";
import { TokenType } from "./token";
import { IntTy, Ty, instantiateTy, isUnit, BOOL, ppTy } from "./ty";
import { InstantiatedFnSig, TypeckResults } from "./typeck";
import { assertUnreachable, assert, todo } from "./util";

export type MirValue = { type: 'int', ity: IntTy, value: number }
    | { type: 'bool', value: boolean }
    | { type: 'str', value: string }
    | { type: 'Local', value: MirLocalId<true> }
    | { type: 'Unreachable' }
    | { type: 'FnDef', value: FnDecl }
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
export type MirStmt = { type: 'Assignment', assignee: MirPlace, value: MirValue }
    | { type: 'BinOp', op: BinaryOp, assignee: MirLocalId<true>, lhs: MirValue, lhsTy: Ty, rhs: MirValue }
    | { type: 'Unary', op: UnaryOp, assignee: MirLocalId<true>, rhs: MirValue }
    | { type: 'Copy', assignee: MirLocalId<true>, place: MirPlace }
    | { type: 'AddrOf', assignee: MirLocalId<true>, place: MirPlace }
    | { type: 'Bitcast', from_ty: Ty, to_ty: Ty, assignee: MirLocalId<true>, value: MirValue }
    | { type: 'Ext', from_ty: Ty, to_ty: Ty, assignee: MirLocalId<true>, value: MirValue }
    | { type: 'Trunc', from_ty: Ty, to_ty: Ty, assignee: MirLocalId<true>, value: MirValue }
    | { type: 'InitArrayLit', assignee: MirLocalId<true>, ty: { type: 'Array' } & Ty, values: MirValue[] }
    | { type: 'InitArrayRepeat', assignee: MirLocalId<true>, ty: { type: 'Array' } & Ty, value: MirValue, count: number };
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
    function lowerMir(): MirBody {
        if (decl.body.type !== 'Block') throw `${decl.sig.name} did not have a block as its body?`;

        const astLocalToMirLocal = new Map<LetDecl | FnParameter, MirLocalId<false>>();
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

        const parameters = [];
        for (const param of decl.sig.parameters) {
            const local = addLocal(typeck.loweredTys.get(param.ty)!, false);
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
                throw new Error(`place was expected, got ${place.type}`);
            }
        }

        function lowerStmt(stmt: Stmt) {
            switch (stmt.type) {
                case 'FnDecl': break; // Nested bodies are only lowered when explicitly requested
                case 'ExternFnDecl':
                    // Extern fns don't have a body, nothing needs to be lowered
                    // TODO: we might want to at the very least validate intrinsic signatures
                    break;
                case 'LetDecl': {
                    const ty = typeck.exprTys.get(stmt.init)!;
                    const local = addLocal(ty, false);
                    astLocalToMirLocal.set(stmt, local);
                    const value = asValue(lowerExpr(stmt.init), ty);
                    block.stmts.push({ type: 'Assignment', assignee: { base: local, projections: [] }, value });
                    break;
                }
                case 'Expr': lowerExpr(stmt.value); break;
                case 'TyAlias': break;
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

        type LowerExprResult = MirValue | ({ type: 'Place' } & MirPlace);

        function lowerExpr(expr: Expr): LowerExprResult {
            switch (expr.type) {
                case 'Number': return { type: 'int', ity: expr.suffix, value: expr.value };
                case 'String': return { type: 'str', value: expr.value };
                case 'Path': {
                    const resolution = resolutions.valueResolutions.get(expr)!;
                    switch (resolution.type) {
                        case 'FnDecl': {
                            return {
                                type: 'FnDef',
                                value: resolution
                            };
                        };
                        case 'FnParam':
                        case 'LetDecl': {
                            const id = astLocalToMirLocal.get(resolution.type === 'LetDecl' ? resolution : resolution.param)!;
                            return { type: 'Place', base: id, projections: [] };
                        }
                        case 'ExternFnDecl': return { type: 'ExternFnDef', value: resolution };
                        case 'Variant': return { type: 'Variant', enum: resolution.enum, variant: resolution.variant };
                        default: assertUnreachable(resolution);
                    }
                }
                case 'Return': {
                    const ret = asValue(lowerExpr(expr.value), typeck.exprTys.get(expr.value)!);
                    return lowerReturnValue(ret);
                }
                case 'Binary': {
                    const lhsTy = typeck.exprTys.get(expr.lhs)!;
                    const lhs = asValue(lowerExpr(expr.lhs), lhsTy);
                    const rhs = asValue(lowerExpr(expr.rhs), typeck.exprTys.get(expr.rhs)!);
                    const res = addLocal(typeck.exprTys.get(expr)!, true);
                    block.stmts.push({ type: 'BinOp', assignee: res, lhs, lhsTy, rhs, op: expr.op });
                    return { type: 'Local', value: res };
                }
                case 'Unary': {
                    const rhs = asValue(lowerExpr(expr.rhs), typeck.exprTys.get(expr.rhs)!);
                    const res = addLocal(typeck.exprTys.get(expr)!, true);
                    block.stmts.push({ type: 'Unary', assignee: res, rhs, op: expr.op });
                    return { type: 'Local', value: res };
                }
                case 'AddrOf': {
                    const pointee = requireAsPlace(lowerExpr(expr.pointee));
                    const res = addLocal(typeck.exprTys.get(expr)!, true);
                    block.stmts.push({ type: 'AddrOf', assignee: res, place: pointee });
                    return { type: 'Local', value: res };
                }
                case 'Assignment': {
                    switch (expr.op) {
                        case TokenType.Assign: {
                            let assignee = requireAsPlace(lowerExpr(expr.target));

                            const value = asValue(lowerExpr(expr.value), typeck.exprTys.get(expr.value)!);
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
                            const rhsTy = typeck.exprTys.get(expr.value)!;
                            const val = asValue(lowerExpr(expr.value), rhsTy);
                            const target = lowerExpr(expr.target);
                            const targetPlace = requireAsPlace(target);
                            const targetVal = asValue(target, typeck.exprTys.get(expr.target)!);
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
                    function instantiateFnSig(sig: InstantiatedFnSig, args: Ty[]): InstantiatedFnSig {
                        return {
                            args: sig.args.map(ty => instantiateTy(ty, args)),
                            parameters: sig.parameters.map(ty => instantiateTy(ty, args)),
                            ret: instantiateTy(sig.ret, args)
                        }
                    }
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
                                default: throw new Error(`unknown intrinsic: ${res.sig.name}`);
                            }
                        }
                    }

                    const callee = lowerExpr(expr.callee);
                    if (callee.type !== 'FnDef' && callee.type !== 'ExternFnDef') {
                        throw new Error('callee must be a FnDef or ExternFnDef');
                    }
                    const res = addLocal(sig.ret, true);

                    const callArgs = expr.args.map(v => asValue(lowerExpr(v), typeck.exprTys.get(v)!));

                    const targetBlock = blocks.length;
                    blocks.push({ stmts: [], terminator: null });

                    block.terminator = { type: 'Call', args: callArgs, assignee: res, decl: callee.value, sig, target: targetBlock };
                    block = blocks[targetBlock];

                    return { type: 'Local', value: res };
                }
                case 'Property': {
                    const val = lowerExpr(expr.target);
                    if (val.type === 'Place') {
                        val.projections.push({ type: 'Field', property: expr.property });
                        return val;
                    } else {
                        let base: MirLocalId;
                        if (val.type !== 'Local') {
                            throw new Error('property base must be a local');
                        } else {
                            base = val.value;
                        }
                        return {
                            type: 'Place',
                            base: base,
                            projections: [{ type: 'Field', property: expr.property }]
                        }
                    }
                }
                case 'Index': {
                    const target = requireAsPlace(lowerExpr(expr.target));
                    const index = asValue(lowerExpr(expr.index), typeck.exprTys.get(expr.index)!);
                    target.projections.push({ type: 'Index', index });
                    return target;
                }
                case 'ArrayLiteral':
                case 'ArrayRepeat': {
                    const exprTy = typeck.exprTys.get(expr)!;
                    if (exprTy.type !== 'Array') {
                        throw new Error('array literal did not produce array type');
                    }

                    const assignee = addLocal(exprTy, true);
                    if (expr.type === 'ArrayLiteral') {
                        block.stmts.push({
                            assignee,
                            type: 'InitArrayLit',
                            ty: exprTy,
                            values: expr.elements.map(e => asValue(lowerExpr(e), typeck.exprTys.get(e)!))
                        });
                    } else {
                        block.stmts.push({
                            assignee,
                            type: 'InitArrayRepeat',
                            ty: exprTy,
                            count: expr.count,
                            value: asValue(lowerExpr(expr.element), typeck.exprTys.get(expr.element)!)
                        });
                    }
                    return { type: 'Local', value: assignee };
                }
                case 'Record': {
                    const fields: RecordFields<MirValue> = expr.fields.map(([key, expr]) => {
                        return [key, asValue(lowerExpr(expr), typeck.exprTys.get(expr)!)];
                    });
                    return {
                        type: 'Record',
                        value: fields
                    }
                }
                case 'Bool': return { type: 'bool', value: expr.value };
                case 'If': {
                    const condition = asValue(lowerExpr(expr.condition), BOOL);
                    const joinedBlock = addBlock();
                    const thenBlock = addBlock();
                    block.terminator = { type: 'Conditional', else: joinedBlock, then: thenBlock, condition };

                    block = blocks[thenBlock];
                    lowerExpr(expr.then);
                    block.terminator = { type: 'Jump', target: joinedBlock };

                    block = blocks[joinedBlock];
                    return UNIT_MIR;
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
                    return UNIT_MIR;
                }
                case 'Tuple': {
                    const elements: MirValue[] = expr.elements.map(expr => {
                        return asValue(lowerExpr(expr), typeck.exprTys.get(expr)!);
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
                default: assertUnreachable(expr);
            }
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
