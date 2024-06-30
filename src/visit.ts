import { Stmt, Expr } from "./parse";
import { assertUnreachable } from "./util";

export function forEachExprInStmt(stmt: Stmt, f: (e: Expr) => void) {
    switch (stmt.type) {
        case 'Expr': forEachExpr(stmt.value, f); break;
        case 'FnDecl': forEachExpr(stmt.body, f); break;
        case 'LetDecl': forEachExpr(stmt.init, f); break;
        case 'TyAlias': break;
    }
}

export function forEachExpr(expr: Expr, f: (e: Expr) => void) {
    f(expr);

    switch (expr.type) {
        case 'Path':
        case 'Number':
        case 'Bool':
        case 'String': break;
        case 'Block': for (const stmt of expr.stmts) forEachExprInStmt(stmt, f); break;
        case 'Return': forEachExpr(expr.value, f); break;
        case 'ArrayLiteral': for (const elem of expr.elements) forEachExpr(elem, f); break;
        case 'ArrayRepeat': forEachExpr(expr.element, f); break;
        case 'Assignment':
            forEachExpr(expr.target, f);
            forEachExpr(expr.value, f);
            break;
        case 'Index':
            forEachExpr(expr.target, f);
            forEachExpr(expr.index, f);
            break;
        case 'Binary':
            forEachExpr(expr.lhs, f);
            forEachExpr(expr.rhs, f);
            break;
        case 'AddrOf': forEachExpr(expr.pointee, f); break;
        case 'Deref': forEachExpr(expr.pointee, f); break;
        case 'Record':
            for (const [, field] of expr.fields) {
                forEachExpr(field, f)
            }
            break;
        case 'FnCall':
            forEachExpr(expr.callee, f);
            for (const arg of expr.args) forEachExpr(arg, f);
            break;
        case 'Property':
            forEachExpr(expr.target, f);
            break;
        case 'If':
            forEachExpr(expr.condition, f);
            forEachExpr(expr.then, f);
            if (expr.else) {
                forEachExpr(expr.else, f);
            }
            break;
        case 'While':
            forEachExpr(expr.condition, f);
            forEachExpr(expr.body, f);
            break;
        case 'Unary':
            forEachExpr(expr.rhs, f);
            break;
        case 'Tuple':
            for (const element of expr.elements) {
                forEachExpr(element, f);
            }
            break;
        case 'Break':
        case 'Continue':
            break;
        case 'Match': {
            forEachExpr(expr.scrutinee, f);
            for (const arm of expr.arms) {
                forEachExpr(arm.body, f);
            }
            break;
        }
        default: assertUnreachable(expr);
    }
}
