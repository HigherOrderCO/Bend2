
# Bend's import system - total environment specification

The import system and environment of the Bend language aims to be simple, usable and not to repeat errors done by other common languages.

If you look at the current import system, you'll see that it works as follows:
- We have Fully qualified names through the path of the file. This means that if our project is at `./`, and we have `./Nat/add`, and inside of that file we define a function `def f()`, it's name for the system is `Nat/add::f`.
- This means that *each definition has a unique identifier*, because it is not possible for two different definitions live in the same file. The counter argument would be to define two `f` function in the `Nat/add` file, but in this case, the only one registered is the last one (i.e last local one overrides).

The system is currently described in the `import-system.md` file that you read before, and locally it is working fine. We don't have ambiguous names or definitions, and things work just fine.

However, for a languague that will come um as a general programming language, we also want to be able to perform external imports. With this in mind, our first try (and the currently implemented one) was to add imports via github links. It is working, and in fact we can import them. But this is not robust enough. So, I designed a new external import system.

## External Import system

This new external import system works via a package index, such as `PyPi`, `Hackage` and `npm`.
If you look closely at the current implementation, you'll see that the packages from github are downloaded, stored into an `bend_packages/` directory similar to `node_modules`. But in the current implementation we're committing the same error as `npm`, that downloads the *entire code*. Therefore, our goal with this new import system with the package index is to *make definitions self-contained and importable as units*. Obviously this brings some versioning issues, that I'll explain in a bit.

With that in mind, I implemented a package index for bend, whose current state is described in `REPORT.md`. Basically, it indexes packages that for now are only published through github. The packages contain definitions, which are the units I told you about. We just merge them together as packages because it is easier for human users and for us to deal with versioning then simply seeing a bunch of definitions that have no grouping. 

In this system, the version of the package *belongs to it's fully qualified name*. Therefore, if I want to import something, I can do it like: `import VictorTaelin/VecAlg#7/List/dot as dot`, and this will grab the library under `VictorTaelin/VecAlg` of version `7`, subdir `List/dot.bend` file. Since the version is part of the name, different versions of the same code have different identifiers. When writing library code, if you omit the version of your import, we simply consider the latest possible (coming from the package index).

This way, we have completely independent definitions that work together as packages in the time of publishing to help visualization, but that can be imported individually. For example, the import above should absolutely *NOT* bring the entire `VecAlg#7` library to the user's computer, it should only bring the needed files, i.e `VictorTaelin/VecAlg#7/List/dot.bend` and it's dependencies.

Note that for this to work, the package index has to expose an API so we can query for individual definitions and full path of dependencies. This means that we should be able to call the API with `VictorTaelin/VecAlg#7/List/dot.bend` and receive back a response like:

```
}
[
  {
    "file": "VictorTaelin/VecAlg#7/List/dot", 
    "content": "content here",
    "dependencies": [
      { "file": "Path/to/dependency", "content": "something",  "dependencies": [] }, 
    ]
]
```

This way we have all we need. The files and the isolated dependencies, without having the entire packages. Then, our import system will write each file to `bend_packages` (similar to node modules) in their correct path so we get the correct fully qualified path and are able to correctly type check the files.



