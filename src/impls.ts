import { AstTy, Impl, ImplItem, Trait, TraitItem, WhereClause } from "./parse";
import { eqTy, ppTy, Ty, TyParamCheck } from "./ty";
import { spanless_bug } from "./error";
import { LoweredWhereClause } from "./typeck";
import { todo } from "./util";

export type EarlyImpls = [AstTy, Impl][];
export type LateImpls = [Ty, Impl][];

export type LateImplLookupResult = { type: 'ImplItem', value: ImplItem } | { type: 'TraitItem', trait: Trait, value: TraitItem } | null;

export function itemInLateImpl(impls: LateImpls, lty: Ty, name: string, where?: LoweredWhereClause): LateImplLookupResult {
    if (lty.type === 'TyParam') {
        if (!where) {
            spanless_bug(`finding impls of ${ppTy(lty)} requires a where clause`);
        }

        for (const bound of where.bounds) {
            if (eqTy(lty, bound.ty, TyParamCheck.StrictEq)) {
                const item = bound.trait.items.find(item => item.sig.name === name);
                if (item) return { type: 'TraitItem', trait: bound.trait, value: item };
            }
        }

        return null;
    } else {
        for (const [implTy, innerImpl] of impls) {
            if (eqTy(lty, implTy, TyParamCheck.IgnoreAgainst)) {
                const item = innerImpl.items.find(item => item.decl.sig.name === name);
                if (item) return { type: 'ImplItem', value: item };
            }
        }
        return null;
    }
}
