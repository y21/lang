# lang

This is my personal language (name TBD).

This mostly only exists so I can play around with my ideas around langdev.
There's no reason for anyone to use this.
Most of the ideas are taken from Rust (and TypeScript to some extent), or at least, that's the idea -- take all the concepts that I like and change them however I like.

### Usage
At this point the compiler is written in TypeScript (eventually it will be rewritten in this language and self-hosted).
So you'll need node.js installed (and clang).
Running `npm i --save-dev && npx tsc` will give you the compiler.

```sh
# it currently just reads the `input` file
$ cat input
function main(): i32 {
    let x = 40;
    let y = 2;
    return x + y;
}

# run the compiler on that file
$ node .
parse: 1.564ms
name res: 0.453ms
typeck: 0.746ms
llir/mir codegen: 0.756ms
clang: 4.332ms

compilation succeeded

# run it
$ ./a.out; echo $?
42
```

You can also get errors
```sh
$ cat input
function main(): i32 {
    return "";
}

$ node .
    return "";
    ^^^^^^^^^  type error: string is not a subtype of i32 (reason: 'Return')
```
