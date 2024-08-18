import path from "path";
import { options } from "./cli";
import { fileFromSpan, SourceMap, Span, spanInfo } from "./span";
import { assert } from "./util";

export function bug(where: Span, what: string): never {
    throw new Bug(where, what);
}

export function spanless_bug(what: string): never {
    throw new Bug(null, what);
}

export function err(where: Span, what: string, note?: string, suggestions?: Suggestion[]): never {
    throw new StandardError(where, what, note, suggestions);
}

export abstract class DiagError extends Error {
    abstract emit(sm: SourceMap): void;
}

export class StandardError extends DiagError {
    constructor(private span: Span, message: string, private note?: string, private suggestions?: Suggestion[]) {
        super(message);
    }
    emit(sm: SourceMap): void {
        emitErrorRaw(
            sm,
            this.span,
            `error: ${this.message}`,
            this.note,
            this.suggestions
        );
    }
}

export class Bug extends DiagError {
    constructor(private span: Span | null, message: string) {
        super(message);
    }
    emit(sm: SourceMap) {
        emitErrorRaw(
            sm,
            this.span ?? null,
            `internal compiler error: ${this.message}`,
            // skip 2 since we aren't interested in the message and the `bug()` call frame
            `backtrace:\n${this.stack?.split('\n').slice(2, 5).join('\n')}`
        );
    }
}

export type Suggestion = {
    message: string,
    replacements: SuggestionReplacement[]
};

export type SuggestionReplacement = {
    span: Span,
    replacement: string
};

function extractLine(sm: SourceMap, span: Span): { line: string, lineStart: number, lineEnd: number, col: number, snipLen: number } {
    let lineStart = sm.source.lastIndexOf('\n', span[0]) + 1;
    let lineEnd = sm.source.indexOf('\n', span[1]);
    const col = span[0] - lineStart;
    const snipLen = span[1] - span[0];
    return {
        line: sm.source.substring(lineStart, lineEnd),
        lineStart,
        lineEnd,
        col,
        snipLen
    }
}

export function emitErrorRaw(sm: SourceMap, span: Span | null, message: string, note?: string, suggestions?: Suggestion[]) {
    const colored = (text: string, color: string) => options.colors ? `${color}${text}\x1b[0m` : text;
    const red = (text: string) => colored(text, '\x1b[1;31m');
    const green = (text: string) => colored(text, '\x1b[1;32m');
    const cyan = (text: string) => colored(text, '\x1b[1;36m');

    console.error(red(message));
    if (span) {
        const file = fileFromSpan(sm, span)!;
        const info = spanInfo(sm.source, span);
        console.error(` -> ${path.basename(file.path)}:${info.fromLine}:${info.fromCol}`);
    }
    console.error();

    if (span) {
        const { line, col, snipLen } = extractLine(sm, span);

        console.error(line);
        console.error(' '.repeat(col) + red('^'.repeat(snipLen)));
    }

    if (note) {
        console.error();
        console.error('note: ' + note);
    }

    if (suggestions) {
        for (const suggestion of suggestions) {
            console.error(cyan('help: ') + suggestion.message);
            console.error();
            assert(suggestion.replacements.length > 0);

            suggestion.replacements.sort((a, b) => a.span[0] - b.span[0]);
            const { line, lineStart, lineEnd } = extractLine(sm, suggestion.replacements[0].span);
            let fixedLine = '';
            let lastEndIndex = 0;
            for (const part of suggestion.replacements) {
                fixedLine += line.slice(lastEndIndex, lastEndIndex + (part.span[0] - lineStart));

                fixedLine += green(part.replacement);
                fixedLine += red(line.slice(part.span[0] - lineStart, part.span[1] - lineStart));
                lastEndIndex = part.span[1];
            }
            fixedLine += line.slice(lastEndIndex - lineStart, lineEnd - lineStart);

            console.error(fixedLine)
        }
    }
}
