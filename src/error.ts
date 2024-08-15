import { options } from "./cli";
import { SourceMap, Span } from "./span";

export function bug(where: Span, what: string): never {
    throw new Bug(where, what);
}

export function spanless_bug(what: string): never {
    throw new Bug(null, what);
}

export function err(where: Span, what: string, note?: string): never {
    throw new StandardError(where, what);
}

export abstract class DiagError extends Error {
    abstract emit(sm: SourceMap): void;
}

export class StandardError extends DiagError {
    constructor(private span: Span, message: string, private note?: string) {
        super(message);
    }
    emit(sm: SourceMap): void {
        emitErrorRaw(
            sm.source,
            this.span,
            `error: ${this.message}`,
            this.note
        );
    }
}

export class Bug extends DiagError {
    constructor(private span: Span | null, message: string) {
        super(message);
    }
    emit(sm: SourceMap) {
        emitErrorRaw(
            sm.source,
            this.span ?? null,
            `internal compiler error: ${this.message}`,
            // skip 2 since we aren't interested in the message and the `bug()` call frame
            `backtrace:\n${this.stack?.split('\n').slice(2, 5).join('\n')}`
        );
    }
}

export function emitErrorRaw(src: string, span: Span | null, message: string, note?: string) {
    const red = (text: string) => options.colors ? `\x1b[1;31m${text}\x1b[0m` : text;

    console.error(red(message));

    if (span) {
        let lineStart = src.lastIndexOf('\n', span[0]);
        let lineEnd = src.indexOf('\n', span[1]);
        const col = span[0] - lineStart;
        const snipLen = span[1] - span[0];
        const line = src.substring(lineStart, lineEnd);

        console.error(line);
        console.error(' '.repeat(col - 1) + red('^'.repeat(snipLen)));
    }

    if (note) {
        console.error();
        console.error('note: ' + note);
    }
}
