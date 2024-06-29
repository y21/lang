import { assert } from "./util";

export type Span = [number, number];

export function joinSpan(a: Span, b: Span): Span {
    return [a[0], b[1]];
}

// zero-based
export type SpanInfo = { fromLine: number, fromCol: number, toLine: number, toCol: number };

export function spanInfo(src: string, span: Span): SpanInfo {
    let prevLineStart = 0;
    let line = 0;
    while (prevLineStart < src.length) {
        const nextNewLine = src.indexOf('\n', prevLineStart);
        assert(nextNewLine > -1);
        let fromLine: number, fromCol: number, toLine: number | null = null, toCol: number | null = null;
        if (nextNewLine > span[0]) {
            fromLine = line;
            fromCol = span[0] - prevLineStart;

            while (prevLineStart < src.length) {
                const nextNewLine = src.indexOf('\n', prevLineStart);
                assert(nextNewLine > -1);
                if (nextNewLine > span[1]) {
                    toLine = line;
                    toCol = span[1] - prevLineStart;
                    break;
                }
                prevLineStart = nextNewLine + 1;
                line++;
            }

            if (toCol === null || toLine === null) {
                // span end points to the end of the file
                toLine = line;
                toCol = src.length - prevLineStart;
            }

            return { fromCol, fromLine, toCol, toLine };
        }

        prevLineStart = nextNewLine + 1;
        line++;
    }
    throw new Error('malformed span');
}

export function ppSpan(src: string, span: Span): string {
    const inf = spanInfo(src, span);
    return `${inf.fromLine + 1}:${inf.fromCol + 1} ${inf.toLine + 1}:${inf.toCol + 1}`;
}
