export type OptLevel = '-O0' | '-O1' | '-O2' | '-O3' | '-O';
export type CliOptions = {
    path: string,
    /**
     * When this is true, skip the `clang` step and just print the LLVM IR (the very last IR we generate) to the console.
     * Currently only used for tests
     */
    printLlirOnly: boolean;
    optLevel: OptLevel,
    verbose: boolean,
    timings: boolean;
    colors: boolean;
};

function parseOptions(): CliOptions {
    let path: string | null = null;
    let optLevel: OptLevel = '-O0';
    let verbose = false;
    let printLlirOnly = false;
    let timings = false;
    let colors = true;
    const args = process.argv.slice(2).values();

    let opt: IteratorResult<string>;
    while (!(opt = args.next()).done) {
        switch (opt.value) {
            case '-O3':
            case '-O2':
            case '-O1':
            case '-O0':
            case '-O': optLevel = opt.value; break;
            case '--print-llir-only': printLlirOnly = true; break;
            case '--timings': timings = true; break;
            case '--verbose': verbose = true; break;
            case '--no-colors': colors = false; break;
            default:
                if (path) {
                    throw new Error('cannot specify an input path twice');
                }
                path = opt.value;
                break;
        }
    }

    path ||= 'input';

    return { path, optLevel, verbose, printLlirOnly, timings, colors };
}

export const options = parseOptions();
