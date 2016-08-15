2nd-Class Values with Bounded Lifetimes
=======================================

First-class functions dramatically increase expressiveness,
at the expense of static guarantees.

In ALGOL or PASCAL, functions could be passed as arguments
but never escape their defining scope. 
Therefore, function arguments could serve as temporary access
tokens or capabilities, enabling callees to perform some 
action, but only for the duration of the call.

In modern languages, such programming patterns are 
no longer available.

The central thrust of this work is to re-introduce 
second-class functions and other values alongside 
first-class entities in modern languages. 

This Scala compiler plug-in exposes a programming model to 
enforce a _no-escape_ policy for certain objects.

There are many potential uses:

- Effects: 
    Objects can serve as capabilities. But we must limit the scope of capabilities to retain control. Compare to Monads, which do not compose well. 
- Region based memory:
    Deallocate and/or reuse memory in a timely manner (note that we do not aim to do this for _all_ allocations, just for big chunks).
- Resource control:
    Ensure that resources such as file handles are properly closed.
- Staging:
    Scope extrusion. We must limit the scope of binders to guarantee well-typed generated code.
- Distributed systems:
    We do not want to serialize large data by accident (see Spores).

The key ideas for combining first- and second-class values in a single language are as follows:

- First-class functions may not refer to second-class values through free variables
- All functions must return first-class values, and only
  first-class values may be stored in object fields or mutable
  variables 

Together, these rules ensure that second-class values never escape their
defining scope.

More details are described in our OOPLA'16 paper:

- [Gentrification Gone too Far? Affordable 2nd-Class Values for Fun and (Co-)Effect](https://www.cs.purdue.edu/homes/rompf/papers/osvald-oopsla16.pdf)

The `coq` subdirectory contains mechanized proofs for the theorems in the paper.

We also provide a modified version of the Scala distribution, where higher-order functions in the standard library (especially collections) are annotated as second class where possible:

- [https://github.com/losvald/scala/tree/esc](https://github.com/losvald/scala/tree/esc)



A High-Level Example
--------------------

If a variable or function parameter is marked `@local`, it will be second-class, and thus it must not escape.

```scala
// For exception handling, we would like to enforce that
// exceptions can only be raised within a try/catch block.

def trycatch(f: @local (Exception => Nothing) => Unit): Unit

// The closure passed to trycatch may not leak its argument.

trycatch { raise =>
  raise(new Exception)  // ok: raise cannot escape
}

// Inside a try block we can use `raise` in safe positions,
// but not in unsafe ones, where it could be leaked.

def safeMethod(@local f: () => Any): Int
def unsafeMethod(f: () => Any): Int

trycatch { raise =>
  safeMethod { () =>
    raise(new Exception)  // ok: closure is safe
  }
  unsafeMethod { () =>
    raise(new Exception)  // not ok
  }
}
```

See the [test suite](library/src/test/scala/scala/tools/escape) for complete code.


Rationale and Background
------------------------

The concept of higher-order and first-class language constructs goes hand in hand. In a higher-order language, many things are first-class: functions, mutable references, etc.

Being first-class means that there are no restrictions on how an object may be used. Functions can be passed to other functions as arguments and returned from other functions. First class reference cells may hold functions or other reference cells.

Lexical scope is central to most modern programming languages. First-class functions _close over_ their defining scope. Hence they are also called closures.

While programming with first-class objects is incredibly useful, it is sometimes _too_ powerful, and one loses some useful guarantees.

For example, in a language without closures, function calls follow a strict stack discipline. A local variable's lifetime ends when the function returns and its space can be reclaimed. Contrast this with higher-order languages, which allocate closure records on the heap. The lifetime of a variable may be indefinite if it is captured by a closure.

Binding the lifetime of (certain -- not all) objects is important. So maybe not all objects should be first class?
