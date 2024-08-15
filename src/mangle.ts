import { spanless_bug } from "./error";
import { FnDecl } from "./parse";
import { ItemPathMap, Resolutions } from "./resolve";
import { instantiateTy, Ty } from "./ty";
import { assertUnreachable, assert } from "./util";

function pathToLlvmSymbol(s: string): string {
    return s.replaceAll('::', '$$')
        .replaceAll('{', '$LB$')
        .replaceAll('}', '$RB');
}

export function mangleTy(itemPathMap: ItemPathMap, ty: Ty): string {
    switch (ty.type) {
        case 'never':
        case 'str':
        case 'bool':
            return ty.type;
        case 'int':
            return (ty.value.signed ? 'i' : 'u') + ty.value.bits;
        case 'Array':
            return `$array$${ty.len}$${mangleTy(itemPathMap, ty.elemTy)}`;
        case 'TyParam':
        case 'TyVid':
        case 'FnDef':
        case 'ExternFnDef':
        case 'TraitFn':
            spanless_bug(`attempted to mangle ${ty.type}`);
        case 'Pointer':
            return `$ptr$${ty.mtb}$${mangleTy(itemPathMap, ty.pointee)}`;
        case 'Alias': {
            let out = mangleTy(itemPathMap, instantiateTy(ty.alias, ty.args));
            if (ty.args.length > 0) {
                out += '$LT$';
                for (let i = 0; i < ty.args.length; i++) {
                    if (i !== 0) out += '$$';
                    out += mangleTy(itemPathMap, ty.args[i]);
                }
                out += '$RT$';
            }
            return out;
        }
        case 'Record': {
            let out = '$LB$';
            for (const [k, v] of ty.fields) {
                out += k + '$$' + mangleTy(itemPathMap, v);
            }
            out += '$RB$';
            return out;
        };
        case 'Tuple': {
            let out = '$LP$';
            for (let i = 0; i < ty.elements.length; i++) {
                if (i !== 0) out += '$$';
                out += mangleTy(itemPathMap, ty.elements[i]);
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

    let mangled = pathToLlvmSymbol(res.itemUniquePathsForCodegen.get(decl)!);

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
            mangled += mangleTy(res.itemUniquePathsForCodegen, args[i]);
        }

        mangled += '$GT$';
    }

    return mangled;
}
