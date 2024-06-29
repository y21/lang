import { inspect as _inspect } from 'util';
import { options } from './cli';

export function assertUnreachable(v: never): never {
    throw 'impossible';
}

export function todo(what?: string): never {
    throw new Error('Todo: ' + what);
}

export function inspect(v: any): string {
    return _inspect(v, { depth: Infinity, colors: options.colors });
}

export function assert(cond: boolean, msg?: string) {
    if (!cond) {
        if (msg) {
            throw new Error(`Assertion failed: ${msg}`);
        } else {
            throw new Error('Assertion failed');
        }
    }
}
