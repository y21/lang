# Charge

Small WIP language that compiles to LLVM IR.

### Usage

At this point the compiler is written in TypeScript (eventually it will be rewritten in charge and self-hosted).
So you'll need node.js installed (and clang).
Running `pnpm install && pnpm build` will compile the compiler.

### Hello World

```sh
$ cat hello-world.chg
mod std;
fn main() {
    std::println("Hello");
}

# Run the compiler on that file
$ pnpm compile hello-world.chg

# Execute the program
$ ./a.out
Hello
```

### Compiler Errors

```sh
$ cat error.chg
fn main(): i32 {
    return "";
}

$ pnpm compile error.chg
    return "";
    ^^^^^^^^^  type error: string is not a subtype of i32 (reason: 'Return')
```

### Features

Modules, Generics, Traits and Pointers/(De)referencing similar to Rust:

```rs
mod std;
use std::fmt::Display;
use std::string::str_concat;
use std::string::String;

fn identity<T>(v: T): T {
    return v;
}

type Rectangle = { width: i32, height: i32 };

impl Display for Rectangle {
    fn to_string(self*): String {
        return str_concat("Area: ", (self*.width * self*.height).to_string().as_str());
    }
}

fn main() {
    let r: Rectangle = identity(.{width: 4, height: 5});
    std::println(r); // prints "Area: 20"
}
```

Enums, Interoperability with C libary functions through the `extern` keyword:

```rs
mod std;
extern "C" fn abs(x: i32): i32;

type Number = enum { NegativeFortyTwo, SomeOtherNumbers };

fn get_value(n: Number): i32 {
    return match n {
        Number::NegativeFortyTwo => -42,
        other => 0 // "other" is the default match arm
    }; // control flow keywords are expressions!
}

fn main() {
    let number = get_value(Number::NegativeFortyTwo);
    std::println(abs(number)); // prints "42"
}
```

### Testing

If working on the language, you can test it against this repository's test suite by running `pnpm test`.
