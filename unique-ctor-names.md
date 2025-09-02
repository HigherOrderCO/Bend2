
So, in bend's system, because of many reasons due to type checking, we want to enforce the following constraint:


Custom Type constructor names HAVE to be unique.

This is a constraint needed because for example, when you reach a constructor name at some point on the type checker, then it is possible to infer it's type by only looking at the constructor name, which makes many inferences possible.

The simplest / naive way to do it is simply prohibit repeated names for constructors on the parser, in a way that this:

```
type A:
  case @X:
  case @Y:

type B:
  case @Z:
  case @Y:
```

Is not allowed.
However, this is a bad solution, because imagine you have many libraries and then you import a library and suddenly your code does not work anymore because someone defined a type with the same constructor as you. This is not viable for users.

So we have to think about new ways of doing that.


The solution for this problem is as follows:
When parsing / import, you'll see that we append the fully qualified names for functions. I.e in `Nat/add.bend`, this:
```
type A:
  case @X:

def f() -> Nat:
  0n
```

becomes `Nat/add::f` in the book. This happens for functions and type definitions, so `A` becomes `Nat/add::A`. However this does not happen for the constructor, so `@X` is just `@X`. 

However, we want to prefix the constructors with their types. So, now we'll have:
`Nat/add::A` and `@A::X`. We can do this automatically in the parser for the type def, because we have the type that it is defining it.

Now we just have to process the rest of the file / terms so we can determine the prefixes correctly.
This should be a separated phase in Adjust.

In this new file, not sure what to call it yet, we need to:
- adjust the whole book, already with the imports and so on.
- in the book, we also have a map of the types and their constructors

So, we look at the term and look to find constructors (i.e the `@ctor{}` syntax that happens either when constructing something or when pattern matching on something of a custom type). Then, if that constructor is unique, that's ok and we add the type prefix missing.
For example:

```
type A:
  case @X:
  case @Y:

def main() -> A:
  return @X
```

In this case, the user does not need to actually write the prefixed version `@A::X` because `@X` is a unique constructor, and we can automatically determine that this should be `@A::X`. Then we automatically add this `@A::X` prefix to it.

And what happens if there is ambiguity?
```
type A:
  case @X:
  case @Y:

type B:
  case @W:
  case @X:

def main() -> A:
  return @X
```

In this case, our function should identify that `@X` is ambiguous, because it can belong either to `@A::X` or `@B::X`. Therefore, we should error out with the message:
`Ambigous constructor @X. It could belong to @A::X or @B::X. Please add the prefix to it.`, something like that and highlight the `@X` that is in the `Loc`.

This means the error should be added to the Error type, added a show function and we need to pass down the Loc's span to correctly highlight the element, which means our function  cannot receive a `noSpan` to begin with.

This way we always have prefixed names, i.e there will be no constructors that have no prefix (because they are either added manually or automatically by this part of the adjust phase).

There are some special cases to deal though. Due to how our import system works, all the types and functions are fully qualified. Some, in file `Nat/something`, if you define:

```
type A:
  case @B:
```

This is qualified to `Nat/something::A`. The constructors should also be fully qualified as `Nat/something::A::B`. This way it is completely unambiguous with every other possible constructor.

Also note that we have to replace all the occurrences of some constructor by it's prefixed version. This means we have to traverse terms. My suggestion is to have a substitution map, where if we have a constructor name such as `B` that turns into `A::B`, we put it in a map where `B => A::B` and then when we have this map complete for all names, we traverse the terms and make the substitution, similar to what happens in the import system for qualified name occurrences.

Actually it is possible that we can implement this TOGETHER with the import system. Let's analyze this possibility as well.


