import { inspect as _inspect } from 'util';
import { options } from './cli';

export function assertUnreachable(v: never): never {
    throw new Error('impossible');
}

/**
 * Removes an element at a given index in constant time (by swapping it with the last one to avoid holes)
 */
export function swapRemove<T>(v: T[], index: number): T {
    const last = v[v.length - 1];
    if (!last) {
        throw new Error('cannot swapRemove on an empty array');
    }
    const element = v[index];
    v[index] = last;
    // this needs to be done at the end to support the case index == v.length - 1
    v.length -= 1;
    return element;
}
export function expectLast<T>(v: T[]): T {
    const lastItem = v[v.length - 1];
    if (lastItem === undefined) {
        throw new Error('called expectLast on empty array');
    }
    return lastItem;
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

export function getOrInsert<K, V>(map: Map<K, V>, key: K, or: () => V) {
    let entry = map.get(key);
    if (!entry) {
        entry = or();
        map.set(key, entry);
    }
    return entry;
}
