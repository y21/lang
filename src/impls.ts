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

export function fnInLateImpl(impls: LateImpls, lty: Ty, name: string): ({ type: 'Fn' } & ImplItem) | null {
    for (const [implTy, innerImpl] of impls) {
        if (eqTy(lty, implTy, TyParamCheck.IgnoreAgainst)) {
            const item = innerImpl.items.find(item => item.decl.sig.name === name);
            if (item) return item;
        }
    }
    return null;
}
