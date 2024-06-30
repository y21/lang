# lang

### Usage
At this point the compiler is written in TypeScript (eventually it will be rewritten in this language and self-hosted).
So you'll need node.js installed (and clang).
Running `npm i --save-dev && npx tsc` will compile the compiler.

```sh
# it currently just reads the `input` file
$ cat input
fn add(a: i32, b: i32): i32 {
    return a + b;
}
fn identity<T>(v: T): T {
    return v;
}
fn main(): i32 {
    return add(identity(40), identity(2));
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
fn main(): i32 {
    return "";
}

$ node .
    return "";
    ^^^^^^^^^  type error: string is not a subtype of i32 (reason: 'Return')
```
