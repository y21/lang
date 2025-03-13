import { bug, spanless_bug } from "./error";
import { FnDecl } from "./parse";
import { Resolutions } from "./resolve";
import { instantiateTy, Ty } from "./ty";
import { assertUnreachable, assert } from "./util";

function pathToLlvmSymbol(s: string): string {
    return s.replaceAll('::', '$$')
        .replaceAll('{', '$LB$')
        .replaceAll('}', '$RB');
}

export function mangleTy(ty: Ty, res: Resolutions): string {
    switch (ty.type) {
        case 'never':
        case 'str':
        case 'bool':
            return ty.type;
        case 'int':
            return (ty.value.signed ? 'i' : 'u') + ty.value.bits;
        case 'Array':
            return `$array$${ty.len}$${mangleTy(ty.elemTy, res)}`;
        case 'Slice':
            return `$slice$${mangleTy(ty.elemTy, res)}`;
        case 'TyParam':
        case 'TyVid':
        case 'FnDef':
        case 'ExternFnDef':
        case 'TraitFn':
            spanless_bug(`attempted to mangle ${ty.type}`);
        case 'Pointer':
            return `$ptr$${ty.mtb}$${mangleTy(ty.pointee, res)}`;
        case 'Alias': {
            let out = pathToLlvmSymbol(res.itemUniquePathsForCodegen.get(ty.decl)!);
            if (ty.args.length > 0) {
                out += '$LT$';
                for (let i = 0; i < ty.args.length; i++) {
                    if (i !== 0) out += '$$';
                    out += mangleTy(ty.args[i], res);
                }
                out += '$RT$';
            }
            return out;
        }
        case 'Record': {
            let out = '$LB$';
            for (const [k, v] of ty.fields) {
                out += k + '$$' + mangleTy(v,res );
            }
            out += '$RB$';
            return out;
        };
        case 'Tuple': {
            let out = '$LP$';
            for (let i = 0; i < ty.elements.length; i++) {
                if (i !== 0) out += '$$';
                out += mangleTy(ty.elements[i], res);
            }
            out += '$RP$';
            return out;
        }
        case 'Enum': return ty.decl.name;
        default: assertUnreachable(ty);
    }
}
export function mangleInstFn(res: Resolutions, decl: FnDecl, args: Ty[]): string {
    if (res.entrypoint === decl) return 'main';

    let mangled = pathToLlvmSymbol(
        res.itemUniquePathsForCodegen.get(decl) || bug(decl.body.span, 'no codegen item path for this fn')
    );

    assert(
        (decl.parent?.generics.length ?? 0) +
        decl.sig.generics.length +
        (decl.parent?.ofTrait ? 1 : 0) === args.length, `mismatched generic args when mangling ${decl.sig.name}`);
    if (args.length > 0) {
        mangled += '$LT$';

        for (let i = 0; i < args.length; i++) {
            if (i !== 0) {
                mangled += '$$';
            }
            mangled += mangleTy(args[i], res);
        }

        mangled += '$GT$';
    }

    return mangled;
}
