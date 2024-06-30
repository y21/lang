// LLVM IR code generation. The main entrypoint is `codegen`, which returns the full IR back as a string,
// ready to be written to a file and for clang to process.
//
// This is the very last step in the compiler. 
// It begins with the entrypoint (the `main` fn), and for every function call it encounters,
// it will monomorphize its MIR (generate a copy of the generic function with type parameters filled in)
// and turn that MIR into LLVM IR.
//
// TODO: this is probably not correct, at least for libraries. The way this is implemented means that
// we never codegen functions that are never called. However, dependants of the library might call it, so we must have
// compiled it.

import { mangleInstFn } from "./mangle";
import { MirBody, MirLocal, MirLocalId, MirPlace, MirValue, astToMir } from "./mir";
import { AstEnum, FnDecl } from "./parse";
import { Resolutions } from "./resolve";
import { TokenType } from "./token";
import { Ty, normalize, UNIT, isUnit } from "./ty";
import { TypeckResults, returnTy } from "./typeck";
import { todo, assertUnreachable } from "./util";

export function codegen(src: string, res: Resolutions, typeck: TypeckResults): string {
    const _codegenCache = new Set<string>();
    const _externDeclarations = new Set<string>();
    let declareSection = '';
    const addExternDecl = (name: string, mkSig: () => string) => {
        if (!_externDeclarations.has(name)) {
            _externDeclarations.add(name);
            declareSection += mkSig();
        }
    };
    let fnSection = '';
    let constSection = '';
    let constCount = 0;
    let nextConstId = () => `@ct.${constCount++}`;

    function llEnum(def: AstEnum): string {
        if (def.variants.length > 256) {
            throw new Error(`enum ${def.name} has too many variants`);
        } else {
            return 'i8';
        }
    }

    function llTy(ty: Ty): string {
        switch (ty.type) {
            case 'bool': return 'i1';
            case 'int': return `i${ty.value.bits}`;
            case 'str': throw new Error('cannot directly lower str type');
            case 'Pointer':
                if (ty.pointee.type === 'str') {
                    return '{i8*, i64}';
                } else {
                    return `${llTy(ty.pointee)}*`;
                }
            case 'ExternFnDef': throw new Error('extern fn in llir lowering');
            case 'TyParam': throw new Error('uninstantiated type parameter in llir lowering');
            case 'Array':
                return `[${ty.len} x ${llTy(ty.elemTy)}]`;
            case 'FnDef':
                todo(ty.type);
            case 'Alias':
                return llTy(normalize(ty));
            case 'Record': return '{' + ty.fields.map(v => llTy(v[1])).join(', ') + '}';
            case 'Tuple': return '{' + ty.elements.map(llTy).join(', ') + '}';
            case 'TyVid':
            case 'never':
                throw new Error(`${ty.type} should not appear in llir lowering`);
            case 'Enum': return llEnum(ty.decl);
        }
    }

    function mirLocal<temporary extends boolean>(mir: MirBody, id: MirLocalId<temporary>): MirLocal<temporary> {
        return mir.locals[id] as MirLocal<temporary>;
    }

    function llValTy(mir: MirBody, val: MirValue): string {
        switch (val.type) {
            case 'Local': {
                const local = mirLocal(mir, val.value);
                if (!local.temporary) {
                    return `${llTy(local.ty)}*`
                } else {
                    return llTy(local.ty);
                }
            }
            case 'int': return `i${val.ity.bits}`;
            case 'str': return '{i8*, i64}';
            case 'bool': return 'i1';
            case 'Unreachable': todo('unreachable ty');
            case 'FnDef':
            case 'ExternFnDef': throw new Error(val.type + ' values need to be treated specially');
            case 'Record': return '{' + val.value.map(v => llValTy(mir, v[1])).join(', ') + '}';
            case 'Tuple': return '{' + val.value.map(v => llValTy(mir, v)).join(', ') + '}';
            case 'Variant': return llEnum(val.enum);
        }
    }

    function codegenFn(decl: FnDecl, args: Ty[]) {
        function inner(decl: FnDecl, args: Ty[]) {

            let _temps = 0;
            let tempLocal = () => _temps++;
            let tempBlock = tempLocal;
            const mir = astToMir(src, mangledName, decl, args, res, typeck);

            const getLocal = <temporary extends boolean>(id: MirLocalId<temporary>): MirLocal<temporary> => {
                return mirLocal(mir, id);
            };

            const parameterList = mir.parameters.map((id) => `${llTy(getLocal(id).ty)} %lt.${id}`).join(', ');
            const rawRetTy = decl.sig.ret ? typeck.loweredTys.get(decl.sig.ret)! : UNIT;
            // only "significant" (= non-unit) types get a return place
            const retTy = !isUnit(rawRetTy) ? mir.locals[0].ty : UNIT;

            let output = `define ${isUnit(retTy) ? 'void' : llTy(retTy)} @${mangledName}(${parameterList}) {\n`;

            function compileValueToLocal(val: MirValue): string {
                switch (val.type) {
                    case 'Local': return `%l.${val.value}`;
                    case 'int':
                    case 'bool': return val.value.toString();
                    case 'str':
                        const ctId = nextConstId();
                        const ctTy = `[${val.value.length} x i8]`;
                        constSection += `${ctId} = private constant ${ctTy} c"${val.value}"\n`;
                        return `{i8* bitcast(${ctTy}* ${ctId} to i8*), i64 ${val.value.length}}`;
                    case 'Unreachable': return 'poison';
                    // At least for now, the variant index has 1:1 mapping to the in-memory representation
                    case 'Variant': return val.variant.toString();
                    case 'FnDef':
                    case 'ExternFnDef': throw new Error(val.type + ' values need to be treated specially');
                    case 'Record':
                    case 'Tuple': {
                        // in the codegen stage, records and tuples are almost identical, so we can largely handle them the same here...
                        //
                        // compile {x: 1i32, y: 2i64} to:
                        //
                        // %t1 = alloca {i32, i64}
                        // %p1 = getelementptr {i32, i64}, {i32, i64}* %t1, i32 0, i32 0
                        // store i32 1, i32* %p1
                        // %p1 = getelementptr {i32, i64}, {i32, i64}* %t1, i32 0, i32 1
                        // store i32 2, i32* %p1
                        // %t3 = load %t1
                        // return %t3
                        const tyS = llValTy(mir, val);
                        const tmp = `%t.${tempLocal()}`;
                        // note: write it to a temporary string first and then append it later, since we might potentially have interleaving writes to `output`
                        // during calls to `compileValueToLocal`
                        let tmpOut = '';
                        tmpOut += `${tmp} = alloca ${tyS}\n`;
                        for (let i = 0; i < val.value.length; i++) {
                            const ptrLocal = `%p.${tempLocal()}`;
                            const valueS = compileValueToLocal(
                                val.type === 'Record' ?
                                    val.value[i][1]
                                    : val.value[i]
                            );
                            const valTyS = llValTy(
                                mir,
                                val.type === 'Record'
                                    ? val.value[i][1]
                                    : val.value[i]
                            );
                            tmpOut += `${ptrLocal} = getelementptr ${tyS}, ${tyS}* ${tmp}, i32 0, i32 ${i}\n`;
                            tmpOut += `store ${valTyS} ${valueS}, ${valTyS}* ${ptrLocal}\n`;
                        }
                        const loadLocal = `%t.${tempLocal()}`;
                        tmpOut += `${loadLocal} = load ${tyS}, ${tyS}* ${tmp}\n`;
                        output += tmpOut;
                        return loadLocal;
                    }
                }
            }

            function compilePlaceExpr(place: MirPlace): { finalTy: Ty, finalLocal: string } {
                const rawBase = mir.locals[place.base];

                let finalLocal: string;
                let finalTy = normalize(rawBase.ty);
                if (rawBase.temporary) {
                    // This could be e.g.:
                    //     _ = f().v.x  where f(): {v:{x:i32}}
                    // 
                    // _1 = f()
                    // _2 = copy {base: _1 /* {v:{x:i32}} */, projections: ['v', 'x']}
                    //
                    // We generally want to codegen these projections as a series of GEP, which requires a pointer operand
                    // so we alloca a new variable that we store the base in.
                    const baseId = `%t.${tempLocal()}`;
                    output += `${baseId} = alloca ${llTy(finalTy)}\n`;
                    output += `store ${llTy(finalTy)} %l.${place.base}, ${llTy(finalTy)}* ${baseId}\n`;
                    finalLocal = baseId;
                } else {
                    // If it's not a temporary, then the base is most likely a local variable.
                    // In any case, `temporary = false` means that it must be alloca'd, so there is no need to do the above,
                    // as we already have a pointer that we can GEP into.
                    finalLocal = `%l.${place.base}`;
                }

                // For the above example f().v.x:
                //
                // ; process base:
                // _1 = f(): {v:{x:i32}}
                // _2 = alloca {v:{x:i32}}
                // store _1 -> _2
                //
                // ; process projections:
                // _3 = getelementptr {v:{x:i32}}, _2, 0, 0      ; _3 = {x: i32}*
                // _4 = getelementptr {x:i32}, _3, 0, 0          ; _4 = i32*
                //
                // _4 gives us the final pointer to the last projected place, the `i32`,
                // which we can finally copy into the assignee.

                for (const projection of place.projections) {
                    const oldBase = finalLocal;
                    const oldTy = finalTy;
                    const oldTyS = llTy(oldTy);
                    finalLocal = `%t.${tempLocal()}`;
                    switch (projection.type) {
                        case 'Field': {
                            let projectedIndex: number;
                            switch (oldTy.type) {
                                case 'Record':
                                    projectedIndex = oldTy.fields.findIndex(v => v[0] === projection.property);
                                    finalTy = normalize(oldTy.fields[projectedIndex][1]);
                                    break;
                                case 'Tuple':
                                    if (typeof projection.property !== 'number') {
                                        throw new Error('non-numeric projection on tuple');
                                    }
                                    projectedIndex = projection.property;
                                    finalTy = normalize(oldTy.elements[projectedIndex]);
                                    break;
                                default:
                                    throw new Error('projection target must be a record or tuple type');
                            }

                            output += `${finalLocal} = getelementptr ${oldTyS}, ${oldTyS}* ${oldBase}, i32 0, i32 ${projectedIndex}\n`;
                            break;
                        }
                        case 'Deref': {
                            output += `${finalLocal} = load ${oldTyS}, ${oldTyS}* ${oldBase}\n`;
                            if (oldTy.type !== 'Pointer') throw new Error('dereferencing non-ptr');
                            finalTy = normalize(oldTy.pointee);
                            break;
                        }
                        case 'Index': {
                            if (finalTy.type !== 'Array') {
                                throw new Error('index target must be an array');
                            }
                            const index = compileValueToLocal(projection.index);
                            const valTyS = llValTy(mir, projection.index);
                            // TODO: bounds checks
                            output += `${finalLocal} = getelementptr ${oldTyS}, ${oldTyS}* ${oldBase}, i32 0, ${valTyS} ${index}\n`;
                            finalTy = finalTy.elemTy;
                            break;
                        }
                        default: assertUnreachable(projection);
                    }
                }

                return { finalTy, finalLocal };
            }

            function compileTemporaryLoop(
                preLoop: () => void,
                header: () => string /* local of the i1 condition */,
                body: () => void,
            ) {
                const headerBlock = `bt.${tempBlock()}`;
                const bodyBlock = `bt.${tempBlock()}`;
                const exitBlock = `bt.${tempBlock()}`;
                preLoop();

                output += `br label %${headerBlock}\n`;
                output += `${headerBlock}:\n`;
                const conditionLocal = header();
                output += `br i1 ${conditionLocal}, label %${bodyBlock}, label %${exitBlock}\n`;

                output += `${bodyBlock}:\n`;
                body();
                output += `br label %${headerBlock}\n`
                output += `${exitBlock}:\n`;
            }

            let writeBB = (name: string) => output += name + ':\n';

            // Prologue: alloca locals for explicit, real locals
            // (temporary locals are created on the fly)
            writeBB('prologue');
            for (let i = 0; i < mir.locals.length; i++) {
                const local = mir.locals[i];
                if (!local.temporary) {
                    output += `%l.${i} = alloca ${llTy(local.ty)}\n`;
                }
            }
            // Also copy the SSA parameters into alloca'd locals
            for (const param of mir.parameters) {
                const local = getLocal(param);
                output += `store ${llTy(local.ty)} %lt.${param}, ${llTy(local.ty)}* %l.${param}\n`;
            }

            output += 'br label %bb.0\n';

            // Begin codegening real blocks
            for (let i = 0; i < mir.blocks.length; i++) {
                const block = mir.blocks[i];
                if (block.stmts.length === 0 && block.terminator === null) {
                    continue;
                }

                output += '\n';
                writeBB(`bb.${i}`);

                for (let j = 0; j < block.stmts.length; j++) {
                    const stmt = block.stmts[j];
                    switch (stmt.type) {
                        case 'Assignment': {
                            const { finalLocal, finalTy } = compilePlaceExpr(stmt.assignee);
                            const valS = compileValueToLocal(stmt.value);
                            output += `store ${llValTy(mir, stmt.value)} ${valS}, ${llTy(finalTy)}* ${finalLocal}\n`;
                            break;
                        }
                        case 'BinOp': {
                            let signed = stmt.lhsTy.type === 'int' && stmt.lhsTy.value.signed;
                            let binOp: string;
                            switch (stmt.op) {
                                case TokenType.Plus: binOp = 'add'; break;
                                case TokenType.Minus: binOp = 'sub'; break;
                                case TokenType.Star: binOp = 'mul'; break;
                                case TokenType.Slash: binOp = signed ? 'sdiv' : 'udiv'; break;
                                case TokenType.Percent: binOp = signed ? 'srem' : 'urem'; break;
                                case TokenType.Lt: binOp = 'icmp ' + (signed ? 'slt' : 'ult'); break;
                                case TokenType.Le: binOp = 'icmp ' + (signed ? 'sle' : 'ule'); break;
                                case TokenType.Gt: binOp = 'icmp ' + (signed ? 'sgt' : 'ugt'); break;
                                case TokenType.Ge: binOp = 'icmp ' + (signed ? 'sge' : 'uge'); break;
                                case TokenType.EqEq: binOp = 'icmp eq'; break;
                                case TokenType.NotEq: binOp = 'icmp ne'; break;
                                default: assertUnreachable(stmt);
                            }
                            const lhsS = compileValueToLocal(stmt.lhs);
                            const rhsS = compileValueToLocal(stmt.rhs);
                            output += `%l.${stmt.assignee} = ${binOp} ${llValTy(mir, stmt.lhs)} ${lhsS}, ${rhsS}\n`;
                            break;
                        }
                        case 'Copy': {
                            const { finalLocal, finalTy } = compilePlaceExpr(stmt.place);
                            output += `%l.${stmt.assignee} = load ${llTy(finalTy)}, ${llTy(finalTy)}* ${finalLocal}\n`;
                            break;
                        }
                        case 'AddrOf': {
                            const { finalLocal, finalTy } = compilePlaceExpr(stmt.place);
                            // Since we already compile place expressions to GEPs and `finalLocal` already is the pointer that we need,
                            // simply emit an identity bitcast
                            output += `%l.${stmt.assignee} = bitcast ${llTy(finalTy)}* ${finalLocal} to ${llTy(finalTy)}*\n`;
                            break;
                        }
                        case 'Bitcast':
                            // compile bitcast<i64, i8*>(0) to
                            //
                            // %tmp = alloca i64
                            // store i64 0, i64* %tmp
                            // %tmp.1 = bitcast i64* %tmp to i8**
                            // %res = load i8*, i8** %tmp.1
                            const fromTyS = llTy(stmt.from_ty);
                            const toTyS = llTy(stmt.to_ty);
                            const castSource = compileValueToLocal(stmt.value);
                            const castSourcePtr = `%t.${tempLocal()}`;
                            output += `${castSourcePtr} = alloca ${fromTyS}\n`;
                            output += `store ${fromTyS} ${castSource}, ${fromTyS}* ${castSourcePtr}\n`;
                            const bitcastPtr = `%t.${tempLocal()}`;
                            output += `${bitcastPtr} = bitcast ${fromTyS}* ${castSourcePtr} to ${toTyS}*\n`;
                            output += `%l.${stmt.assignee} = load ${toTyS}, ${toTyS}* ${bitcastPtr}\n`;
                            break
                        case 'Unary':
                            switch (stmt.op) {
                                case TokenType.Not:
                                    const rhs = compileValueToLocal(stmt.rhs);
                                    output += `%l.${stmt.assignee} = xor i1 ${rhs}, true\n`
                                    break;
                                default: assertUnreachable(stmt);
                            }
                            break;
                        case 'Ext': {
                            if (stmt.from_ty.type !== 'int' || stmt.to_ty.type !== 'int') {
                                throw new Error('ext intrinsic only works on int types');
                            }
                            let instruction = stmt.from_ty.value.signed ? 'sext' : 'zext';
                            const fromTyS = llTy(stmt.from_ty);
                            const toTyS = llTy(stmt.to_ty);
                            const valueS = compileValueToLocal(stmt.value);
                            output += `%l.${stmt.assignee} = ${instruction} ${fromTyS} ${valueS} to ${toTyS}\n`;
                            break;
                        }
                        case 'Trunc': {
                            if (stmt.from_ty.type !== 'int' || stmt.to_ty.type !== 'int') {
                                throw new Error('trunc intrinsic only works on int types');
                            }
                            const fromTyS = llTy(stmt.from_ty);
                            const toTyS = llTy(stmt.to_ty);
                            const valueS = compileValueToLocal(stmt.value);
                            output += `%l.${stmt.assignee} = trunc ${fromTyS} ${valueS} to ${toTyS}\n`;
                            break;
                        }
                        case 'InitArrayRepeat': {
                            const arrayLocal = `%t.${tempLocal()}`;
                            const counterLocal = `%t.${tempLocal()}`;
                            const arrayTyS = llTy(stmt.ty);
                            const valTyS = llTy(stmt.ty.elemTy);
                            const count = stmt.count;
                            const value = compileValueToLocal(stmt.value);

                            // TODO: we can special case with a memset for {i,u}8-32; it accepts up to an int
                            // For now, just generate a loop that initializes each element.
                            compileTemporaryLoop(
                                () => {
                                    output += `${arrayLocal} = alloca ${arrayTyS}\n`
                                    output += `${counterLocal} = alloca i32\n`;
                                    output += `store i32 0, i32* ${counterLocal}\n`;
                                },
                                () => {
                                    const loadTemp = `%t.${tempLocal()}`;
                                    const conditionTemp = `%t.${tempLocal()}`;
                                    output += `${loadTemp} = load i32, i32* ${counterLocal}\n`
                                    output += `${conditionTemp} = icmp ult i32 ${loadTemp}, ${count}\n`;
                                    return conditionTemp;
                                },
                                () => {
                                    const ptrLocal = `%t.${tempLocal()}`;
                                    const curCounterLocal = `%t.${tempLocal()}`;
                                    const addLocal = `%t.${tempLocal()}`;
                                    output += `${curCounterLocal} = load i32, i32* ${counterLocal}\n`
                                    output += `${ptrLocal} = getelementptr ${arrayTyS}, ${arrayTyS}* ${arrayLocal}, i32 0, i32 ${curCounterLocal}\n`;
                                    output += `store ${valTyS} ${value}, ${valTyS}* ${ptrLocal}\n`;
                                    output += `${addLocal} = add i32 ${curCounterLocal}, 1\n`;
                                    output += `store i32 ${addLocal}, i32* ${counterLocal}\n`;
                                },
                            );

                            // Array local is fully initialized. Finally, load it.
                            output += `%l.${stmt.assignee} = load ${arrayTyS}, ${arrayTyS}* ${arrayLocal}\n`;

                            break;
                        }
                        case 'InitArrayLit': {
                            const arrayLocal = `%t.${tempLocal()}`;
                            const arrayTyS = llTy(stmt.ty);
                            const valTyS = llTy(stmt.ty.elemTy);
                            output += `${arrayLocal} = alloca ${arrayTyS}\n`;
                            for (let i = 0; i < stmt.values.length; i++) {
                                const val = compileValueToLocal(stmt.values[i]);
                                const ptrLocal = `%t.${tempLocal()}`;
                                output += `${ptrLocal} = getelementptr ${arrayTyS}, ${arrayTyS}* ${arrayLocal}, i32 0, i32 ${i}\n`;
                                output += `store ${valTyS} ${val}, ${valTyS}* ${ptrLocal}\n`;
                            }
                            output += `%l.${stmt.assignee} = load ${arrayTyS}, ${arrayTyS}* ${arrayLocal}\n`;
                            break;
                        }
                        default: assertUnreachable(stmt);
                    }
                }

                // Process terminator
                const terminator = block.terminator;
                if (terminator) {
                    switch (terminator.type) {
                        case 'Return':
                            if (isUnit(retTy)) {
                                output += 'ret void\n';
                            } else {
                                const tyS = llTy(retTy);
                                const temp = tempLocal();
                                output += `%ret.${temp} = load ${tyS}, ${tyS}* %l.0\n`;
                                output += `ret ${tyS} %ret.${temp}\n`;
                            }
                            break;
                        case 'Call':
                            const parameterList = terminator.sig.parameters.map((ty) => llTy(ty)).join(', ');
                            let mangledName: string;
                            switch (terminator.decl.type) {
                                case 'FnDecl': {
                                    const calleeMangled = mangleInstFn(terminator.decl, terminator.sig.args);
                                    codegenFn(terminator.decl, terminator.sig.args);
                                    // NB: don't write to `output` here before the `argList` mapping, since that may compile values
                                    mangledName = calleeMangled;
                                    break;
                                }
                                case 'ExternFnDecl': {
                                    addExternDecl(terminator.decl.sig.name, () => {
                                        const ret = returnTy(terminator.decl.sig, typeck)!;
                                        return `declare ${isUnit(ret) ? 'void' : llTy(ret)} @${terminator.decl.sig.name}(${parameterList})\n`;
                                    });
                                    mangledName = terminator.decl.sig.name;
                                    break;
                                }
                                default: assertUnreachable(terminator.decl);
                            }

                            const argList = terminator.args.map(arg => `${llValTy(mir, arg)} ${compileValueToLocal(arg)}`).join(', ');
                            if (isUnit(terminator.sig.ret)) {
                                // Annoying hack: we generally codegen functions that return unit as `void()*`, however
                                // we also generally treat ZSTs as equivalent to `{}` and old versions of LLVM error on
                                // `call {} @fnThatReturnsVoid()`.
                                // So just bitcast void()* to {}()*
                                output += `%l.${terminator.assignee} = call {} bitcast(void(${parameterList})* @${mangledName} to {}(${parameterList})*)(${argList})\n`;
                            } else {
                                output += `%l.${terminator.assignee} = call ${llTy(terminator.sig.ret)} @${mangledName}(${argList})\n`;
                            }
                            output += `br label %bb.${terminator.target}\n`;
                            break;
                        case 'Conditional': {
                            const condition = compileValueToLocal(terminator.condition);
                            output += `br i1 ${condition}, label %bb.${terminator.then}, label %bb.${terminator.else}\n`
                            break;
                        }
                        case 'Jump': {
                            output += `br label %bb.${terminator.target}\n`;
                            break;
                        }
                        default: assertUnreachable(terminator)
                    }
                }
            }

            output += '\n}\n\n';

            return output;
        }

        const mangledName = mangleInstFn(decl, args);
        if (_codegenCache.has(mangledName)) return;
        _codegenCache.add(mangledName);
        const code = inner(decl, args)
        fnSection += code;
    }

    // TODO: validate entrypoint fn? like no generics etc?
    codegenFn(res.entrypoint, []);
    return declareSection + '\n' + constSection + '\n' + fnSection;
}
