// This file defines and implements general impl resolution.
// There are two kinds of impls that are used at different times in the compiler:
//
// Early impls are used during early name resolution when we have enough information at that time. For example:
//
//     Foo::bar(..);
//
// Since at name resolution time we know what `Foo` refers to, we can fully resolve `Foo::bar`.
//
// When we have method calls, we cannot resolve them during name resolution (for `x.bar()`, we need to know the type of `x´)
// and instead do this during typechecking with late impls.

import { AstTy, Impl, ImplItem } from "./parse";
import { TypeResolution, TypeResolutions } from "./resolve";
import { eqTy, Ty, TyParamCheck } from "./ty";

export type EarlyImpls = [AstTy, Impl][];
export type LateImpls = [Ty, Impl][];

export function addEarlyImpl(impls: EarlyImpls, ty: AstTy, impl: Impl) {
    impls.push([ty, impl]);
}

function astTyEq(res: TypeResolutions, lty: AstTy, rty: AstTy): boolean {
    const lres = res.get(lty);
    const rres = res.get(rty);
    if (lres && rres) {
        return lres === rres;
    } else if (lty.type === 'Array' && rty.type === 'Array') {
        return lty.len === rty.len && astTyEq(res, lty.elemTy, rty.elemTy);
    } else if (lty.type === 'Pointer' && rty.type === 'Pointer') {
        return lty.mtb === rty.mtb && astTyEq(res, lty.pointeeTy, rty.pointeeTy);
    } else if (lty.type === 'Record' && rty.type === 'Record') {
        return lty.fields.length === rty.fields.length && lty.fields.every(([lprop, lty], idx) => {
            return lprop === rty.fields[idx][0] && astTyEq(res, lty, rty.fields[idx][1]);
        });
    } else if (lty.type === 'Tuple' && rty.type === 'Tuple') {
        return lty.elements.length === rty.elements.length && lty.elements.every((lty, idx) => astTyEq(res, lty, rty.elements[idx]));
    } else {
        return false;
    }
}

export function itemInEarlyImpls(impls: EarlyImpls, tyRes: TypeResolutions, ty: TypeResolution, name: string): ImplItem | null {
    for (const [implTy, impl] of impls) {
        const resolved = tyRes.get(implTy);
        if (resolved === ty) {
            const item = impl.items.find(item => item.decl.sig.name === name);
            if (item) return item;
        }
    }
    return null;
}

export function fnInLateImpl(impls: LateImpls, lty: Ty, name: string): ({ type: 'Fn' } & ImplItem) | null {
    for (const [implTy, innerImpl] of impls) {
        if (eqTy(lty, implTy, TyParamCheck.IgnoreAgainst)) {
            const item = innerImpl.items.find(item => item.decl.sig.name === name);
            if (item) return item;
        }
    }
    return null;
}
