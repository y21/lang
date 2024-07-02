import { Stmt, Expr } from "./parse";
import { assertUnreachable } from "./util";

export function visitInStmt(stmt: Stmt, forExpr: (e: Expr) => void, forStmt: (s: Stmt) => void) {
    forStmt(stmt);

    switch (stmt.type) {
        case 'Expr': visitInExpr(stmt.value, forExpr, forStmt); break;
        case 'FnDecl': visitInExpr(stmt.body, forExpr, forStmt); break;
        case 'LetDecl': {
            if (stmt.init) {
                visitInExpr(stmt.init, forExpr, forStmt);
            }
            break;
        }
        case 'TyAlias': break;
    }
}

export function visitInExpr(expr: Expr, forExpr: (e: Expr) => void, forStmt: (s: Stmt) => void) {
    forExpr(expr);

    switch (expr.type) {
        case 'Path':
        case 'Number':
        case 'Bool':
        case 'String':
        case 'ByteCharacter': break;
        case 'Block':
            for (const stmt of expr.stmts) visitInStmt(stmt, forExpr, forStmt);
            if (expr.tailExpr) visitInExpr(expr.tailExpr, forExpr, forStmt);
            break;
        case 'Return': visitInExpr(expr.value, forExpr, forStmt); break;
        case 'ArrayLiteral': for (const elem of expr.elements) visitInExpr(elem, forExpr, forStmt); break;
        case 'ArrayRepeat': visitInExpr(expr.element, forExpr, forStmt); break;
        case 'Assignment':
            visitInExpr(expr.target, forExpr, forStmt);
            visitInExpr(expr.value, forExpr, forStmt);
            break;
        case 'Index':
            visitInExpr(expr.target, forExpr, forStmt);
            visitInExpr(expr.index, forExpr, forStmt);
            break;
        case 'Binary':
            visitInExpr(expr.lhs, forExpr, forStmt);
            visitInExpr(expr.rhs, forExpr, forStmt);
            break;
        case 'AddrOf': visitInExpr(expr.pointee, forExpr, forStmt); break;
        case 'Deref': visitInExpr(expr.pointee, forExpr, forStmt); break;
        case 'Record':
            for (const [, field] of expr.fields) {
                visitInExpr(field, forExpr, forStmt);
            }
            break;
        case 'FnCall':
            visitInExpr(expr.callee, forExpr, forStmt);
            for (const arg of expr.args) visitInExpr(arg, forExpr, forStmt);
            break;
        case 'Property':
            visitInExpr(expr.target, forExpr, forStmt);
            break;
        case 'If':
            visitInExpr(expr.condition, forExpr, forStmt);
            visitInExpr(expr.then, forExpr, forStmt);
            if (expr.else) {
                visitInExpr(expr.else, forExpr, forStmt);
            }
            break;
        case 'While':
            visitInExpr(expr.condition, forExpr, forStmt);
            visitInExpr(expr.body, forExpr, forStmt);
            break;
        case 'Unary':
            visitInExpr(expr.rhs, forExpr, forStmt);
            break;
        case 'Tuple':
            for (const element of expr.elements) {
                visitInExpr(element, forExpr, forStmt);
            }
            break;
        case 'Break':
        case 'Continue':
            break;
        case 'Match': {
            visitInExpr(expr.scrutinee, forExpr, forStmt);
            for (const arm of expr.arms) {
                visitInExpr(arm.body, forExpr, forStmt);
            }
            break;
        }
        case 'MethodCall': {
            for (const arg of expr.args) visitInExpr(arg, forExpr, forStmt);
            visitInExpr(expr.target, forExpr, forStmt);
            break;
        }
        default: assertUnreachable(expr);
    }
}
