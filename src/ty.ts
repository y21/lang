import { RecordFields, FnDecl, TyAliasDecl, ExternFnDecl, Mutability, genericsOfDecl, AstEnum, Impl, Trait, } from "./parse";
import { assert } from "./util";

export type RecordType = { type: 'Record', fields: RecordFields<Ty> };
export type Bits = 8 | 16 | 32 | 64;
export type IntTy = { signed: boolean, bits: Bits };
export type Variant = { name: string };
export type Ty = ({ flags: TypeFlags }) & ({ type: 'TyVid', id: number }
    | { type: 'Tuple', elements: Ty[] }
    | { type: 'never' }
    | { type: 'bool' }
    | { type: 'int', value: IntTy }
    | { type: 'str' }
    | { type: 'Array', elemTy: Ty, len: number }
    | { type: 'TyParam', id: number, parentItem: FnDecl | TyAliasDecl | ExternFnDecl | Impl | Trait }
    | { type: 'FnDef', decl: FnDecl }
    | { type: 'ExternFnDef', decl: ExternFnDecl }
    | { type: 'Pointer', mtb: Mutability, pointee: Ty }
    | RecordType
    | { type: 'Alias', decl: TyAliasDecl, alias: Ty, args: Ty[] }
    | { type: 'Enum', decl: AstEnum });

export type TypeFlags = number;
export const TYPARAM_MASK = 0b01;
export const TYVID_MASK = 0b10;
export const EMPTY_FLAGS = 0;
export function hasTyParam(ty: Ty): boolean {
    return (ty.flags & TYPARAM_MASK) !== 0;
}
export function withoutTyParam(flags: TypeFlags): TypeFlags {
    return flags & ~TYPARAM_MASK;
}
export function withoutTyVid(flags: TypeFlags): TypeFlags {
    return flags & ~TYVID_MASK;
}
export function hasTyVid(ty: Ty): boolean {
    return (ty.flags & TYVID_MASK) !== 0;
}
export function removeTyVid(ty: Ty): Ty {
    ty.flags &= ~TYVID_MASK;
    return ty;
}
export const I8: Ty & { type: 'int' } = { type: 'int', flags: EMPTY_FLAGS, value: { signed: true, bits: 8 } };
export const U8_PTR: Ty & { type: 'Pointer' } = { type: 'Pointer', mtb: 'imm', flags: EMPTY_FLAGS, pointee: { type: 'int', value: { bits: 8, signed: false }, flags: EMPTY_FLAGS } };
export const I16: Ty & { type: 'int' } = { type: 'int', flags: EMPTY_FLAGS, value: { signed: true, bits: 16 } };
export const I32: Ty & { type: 'int' } = { type: 'int', flags: EMPTY_FLAGS, value: { signed: true, bits: 32 } };
export const I64: Ty & { type: 'int' } = { type: 'int', flags: EMPTY_FLAGS, value: { signed: true, bits: 64 } };
export const U8: Ty & { type: 'int' } = { type: 'int', flags: EMPTY_FLAGS, value: { signed: false, bits: 8 } };
export const U16: Ty & { type: 'int' } = { type: 'int', flags: EMPTY_FLAGS, value: { signed: false, bits: 16 } };
export const U32: Ty & { type: 'int' } = { type: 'int', flags: EMPTY_FLAGS, value: { signed: false, bits: 32 } };
export const U64: Ty & { type: 'int' } = { type: 'int', flags: EMPTY_FLAGS, value: { signed: false, bits: 64 } };
export const UNIT: Ty & { type: 'Tuple' } = { type: 'Tuple', flags: EMPTY_FLAGS, elements: [] };
export const NEVER: Ty & { type: 'never' } = { type: 'never', flags: EMPTY_FLAGS };
export const BOOL: Ty & { type: 'bool' } = { type: 'bool', flags: EMPTY_FLAGS };
export const STR_SLICE: Ty & { type: 'Pointer' } = { type: 'Pointer', mtb: 'imm', flags: EMPTY_FLAGS, pointee: { type: 'str', flags: EMPTY_FLAGS } };

export function isUnit(ty: Ty): boolean {
    return ty.type === 'Tuple' && ty.elements.length === 0;
}

/**
 * Pretty prints a type. This is *exclusively* for error reporting.
 */
export function ppTy(ty: Ty): string {
    switch (ty.type) {
        case 'int':
            return (ty.value.signed ? 'i' : 'u') + ty.value.bits;
        case 'never':
        case 'bool':
        case 'str':
            return ty.type;
        case 'Array':
            return `${ppTy(ty.elemTy)}[${ty.len}]`;
        case 'Pointer':
            return `${ppTy(ty.pointee)}*`
        case 'TyParam': return genericsOfDecl(ty.parentItem)[ty.id];
        case 'TyVid': return `?${ty.id}t`;
        case 'FnDef':
            return `fn ${ty.decl.sig.name}(...)`;
        case 'ExternFnDef':
            return `extern "${ty.decl.abi}" fn ${ty.decl.sig.name}(...)`;
        case 'Record': {
            let out = '{';
            for (let i = 0; i < ty.fields.length; i++) {
                if (i !== 0) {
                    out += ',';
                }
                out += `${ty.fields[i][0]}: ${ppTy(ty.fields[i][1])}`;
            }
            return out + '}';
        }
        case 'Alias':
            if (ty.args.length === 0) return ty.decl.name;
            else return `${ty.decl.name}<${ty.args.map(ty => ppTy(ty)).join(', ')}>`;
        case 'Tuple': return `(${ty.elements.map(ppTy).join(', ')})`;
        case 'Enum': return ty.decl.name;
    }
}

// creates a new type with type parameters replaced with the provided args
export function instantiateTy(ty: Ty, args: Ty[]): Ty {
    // Fast path: type flags can instantly tell us if this type doesn't have any type parameters
    if (!hasTyParam(ty)) return ty;

    switch (ty.type) {
        case 'Alias': {
            let flags = EMPTY_FLAGS;
            const instArgs: Ty[] = [];
            for (const arg of ty.args) {
                const inst = instantiateTy(arg, args);
                flags |= inst.flags;
                instArgs.push(inst);
            }
            return {
                ...ty,
                flags,
                args: instArgs,
            };
        }
        case 'TyVid':
        case 'int':
        case 'never':
        case 'str':
        case 'bool':
            // simple cases: nothing to instantiate
            return ty;
        case 'TyParam':
            assert(ty.id < args.length, 'type parameter index out of bounds');
            return args[ty.id];
        case 'Array': {
            const elemTy = instantiateTy(ty, args);
            return { ...ty, flags: elemTy.flags, elemTy };
        }
        case 'FnDef':
        case 'ExternFnDef':
            throw new Error('attempted to instantiate FnDef');
        case 'Pointer': {
            const pointee = instantiateTy(ty.pointee, args);
            return { ...ty, flags: pointee.flags, pointee };
        }
        case 'Record': {
            let flags = EMPTY_FLAGS;
            const fields: RecordFields<Ty> = [];

            for (const [key, value] of ty.fields) {
                const ty = instantiateTy(value, args);
                flags |= ty.flags;
                fields.push([key, ty]);
            }

            return { flags, type: 'Record', fields: fields };
        }
        case 'Tuple': {
            let flags = EMPTY_FLAGS;
            const elements: Ty[] = [];

            for (const element of ty.elements) {
                const ty = instantiateTy(element, args);
                flags |= ty.flags;
                elements.push(ty);
            }

            return { type: 'Tuple', flags, elements };
        }
        case 'Enum': return ty;
    }
}

// For type aliases, instantiates and returns the aliased type. E.g.
//
//     type X<T> = { v: T }
//
// Calling `normalize(X<i32>)` returns `{ v: i32 }`.
// For any other kind of type, this just returns it unchanged.
export function normalize(ty: Ty): Ty {
    while (ty.type === 'Alias') {
        ty = instantiateTy(ty.alias, ty.args);
    }

    return ty;
}
