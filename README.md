# nox

This is the repository for a custom interpreted language named nox.

## State of the language

This is not meant to be used as a real language, but rather to serve as example and (hopefully) possible reference for implementing a bytecode-based lua-like language.

## Overview

The following features are currently implemented :

- expressions, global variables, functions with local variables :
```
x = 0
y = 1
fn f(a, x)
    x += a
    y += a
end
f(2, 0)
f(5, 9)
return a + b
```
returns `7`

- while and for loops, capturing variables :
```
x = 0
i = 0
while i != 5
    x += i
end
return x
```
returns `10`

```
fn range(a, b) # returns an iterator
    it = a
    fn iter() # this function captures it and b
        if it == b
            return nil
        else
            it += 1
            return it - 1
        end
    end
    return iter
end

x = 0
for i in range(0, 5) # loop until iter returns nil
    x += i
end
return x
```
returns `10`

- tables (via a garbage collector) :
```
t1 = {}
t2 = { x = 5, y = "hello" }
t1.world = "hello"
t2[8] = t1["world"] == t2.y
return t2[8]
```
returns `true`

## Syntax

The exact grammar of the language is described in the [nox.g4](./nox.g4) file, although this is not exact (e.g. identifiers accept unicode characters, or the handling of escape sequences in strings is not described).
