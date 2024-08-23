import { AstTy, Impl, ImplItem } from "./parse";
import { eqTy, Ty, TyParamCheck } from "./ty";

export type EarlyImpls = [AstTy, Impl][];
export type LateImpls = [Ty, Impl][];

export function itemInLateImpl(impls: LateImpls, lty: Ty, name: string): ImplItem | null {
    for (const [implTy, innerImpl] of impls) {
        if (eqTy(lty, implTy, TyParamCheck.IgnoreAgainst)) {
            const item = innerImpl.items.find(item => item.decl.sig.name === name);
            if (item) return item;
        }
    }
    return null;
}
