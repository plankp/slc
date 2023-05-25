# slc -- Standard Library

Since slc organizes units of code into modules,
the standard library is just a whole bunch of modules.

## Build instructions

Once you have `slc` built,
invoke the following command within the current directory.

```
$ slc *.sl
```

## Usage instructions

When compiling your program that uses these modules,
it is recommended that you use the `-I` flag instead of explicitly providing them as part of the input files.

So, say you are compiling `Main.sl`,
and that's the entry point of your program,
do the following.

```
$ slc -I stdlib -entry Main Main.sl
```
