(Work in progress)

C3d will process some definitions in a header file and ouput a 3d file
for them. The way to choose which definitions and how they should be
interpreted is via a set of attributes, detailed below. C3d will also
produce a header file with all the attributes erased, which can be
consumed by compilers without support for C11 attributes.

The supported types on which C3d acts are `struct`s (-> 3d `struct`),
`union`s (-> 3d `casetype`) and `enum`s (-> 3d `enum`).

Supported Attributes
====================

On Types
--------

- `everparse::process`: marks a struct/union/enum to be processed by
the plugin. Needed on every relevant type. This needs an expression
argument, though it is ignored, we recommend just passing 1 as in
everparse::process(1)

- `everparse::entrypoint`: marks a struct/union as a 3d entrypoint.

- `everparse::parameter`: adds a parameter to this type in the 3d
output. The type is unaffected by this parameter in the processed C
code. The argument must be a type followed by a name, so only simple
declarators such as `int x` or `char *p` work. Function pointers and
arrays are not supported here.

- `everparse::mutable_parameter`: as above, but marks the parameter mutable
so it can be affected by actions.

- `everparse::where`: adds a where clause to the 3d output of this
type. The argument should be a C expression representing a condition.
If several `where` attributes are present, they are conjoined in the 3d
output.

- `everparse::switch`: only used for unions. Declares a parameter to
the type, and at the same time stated that this parameter determines
the case of the union. The generated 3d code has a switch on this
parameter in the body. All fields of the union must be marked with
`everparse::case`.

On Fields
---------

- `everparse::constraint`: this attribute appears on fields. It takes as
argument a C expresion representing a 3d constraint, which is then used
for the relevant 3d field.

- `everparse::case`: takes an expression parameter `e`, and declares
that this case of the union is the one used when the switch parameter
has the same value as `e`.

- `everparse::default`: similar to `everparse::case`, but marks the
default case.

- `everparse::with`: instantiate a parameter on the type of this
field. If we have some struct S with a parameter, the parameter only
makes sense at the 3d level, and is completely gone at the C level.
Hence if we have a field `S x` in another struct, we need a parameter
instantiation to generate the 3d output. This attribute does exactly
that. Several `everparse::with` attributes can be used for types with
several parameters (in order).

- `everparse::byte_size`: used to specify the byte size of an array

- `everparse::byte_size_at_most`:

- `everparse::on_success`: takes as argument a *block*, a piece of code
to be executed when parsing this field/case succeeds. The code is copied
verbatim into the 3d output and disappears in the C code. The syntax is
roughly `everparse::on_success(^{s1; s2; ... sN})`. The caret is what
marks a block.

- `everparse::on_failure`: idem above, but for failure.

High level architecture
=======================

Several attributes are registered (via `ParsedAttrInfoRegistry::Add`) to
have a custom action when they are parsed (as well as specify how their
arguments should be parsed, possible after Jonathan's clang patch).

These attributes handlers slap an AnnotAttr on the AST nodes with a
*string* representing the attribute. We cannot add custom data for now,
so we store at this point whatever needs to be printed in the 3d output.

C3dVisitor traverses the parsed file and its definitions, outputting
3d code and editing the RewriteBuffer of the input file to remove the
attributes. It simply prints syntax such as `casetype` and braces,
parentheses, etc, and interleaves the strings from the AnnotAttrs where
needed (e.g., for a field of a struct.)
