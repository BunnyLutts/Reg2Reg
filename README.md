# Reg2Reg

A proof of the translation from regular expression to simplied regular expression.

The theoretical assignment of PL.

## How to contribute (for team members)

Clone this repo:

```bash
git clone git@github.com:BunnyLutts/Reg2Reg.git
cd Reg2Reg
```

Create your own branch:

```bash
git checkout -b dev_${Your_name}
```

First init the environment:

```bash
make depend
make
```

Then just do something to `Assignment/Reg2Reg.v`.

```bash
git add Assignment/Reg2Reg.v
git commit -m "${Your_Message}"
```

When finished,

```bash
git push --set-upstream origin dev_${Your_name}
```

And you can create a pull request.

When you want to update your branch with main:

```bash
git checkout main
git pull
git checkout dev_${Your_name}
git merge main
```

## Explanation

Our work simplifiy general regular expression into a standard form:

```
// General Form
RegEx 	-> EmptySet
	-> EmptyStr		// ''
	-> Optional RegEx	// '?<r>'
	-> Char Judge		// specific char
	-> Concat RegEx RegEx 	// '<r1><r2>'
	-> Union RegEx RegEx	// '<r1>|<r2>'
	-> String Str
	-> Plus RegEx		// '<r>+'
	-> Star RegEx		// '<r>*'
Judge: Char -> Prop
String: list Char
Char: Type

// Standard Form
RegEx 	-> EmptyStr
	-> Char Judge
	-> Concat RegEx RegEx
	-> Union RegEx RegEx
	-> Start RegEx
Judge: Char -> Prop
Char: Type
```

To achieve ideal outcome, we do this transform for the general form:

```
match re_general:
    EmptySet => Empty		// Nothing
    EmptyStr => EmptyStr	// Nothing to do
    Optional re => 		// Here we let bool(Empty) = False, re' = transform re
	re' ? Union EmptyStr re' : EmptyStr
    Concat re1 re2 =>		// Ensure correctness (No Concat or Union of Empty)
	re1' && re2' ? Concat re1' re2' : Empty
    Union re1 re2 =>
	re1' && re2' ? Union re1' re2' : 
	re1' ? re1' : re2' ? re2' : Empty
    String str => "Expand str to Concat of Char"
    Plus re =>
	re' ? Concat re' (Star re') : Empty
    Star re =?
	re' ? Star re' : EmptyStr
```

Generally, the transformation do such two things:
+ Unfold `Optional` and `Plus`
+ Ensure no Empty in Concat and Union

Now we begin to verify it. Firstly we introduce some lemmas:
+ `set_prod_equiv`: Transitivity of equivalence over product
+ `set_prod_equiv_left/right`: Specialize `set_prod_equiv`
+ `set_prod_left/right_empty`: Unit element of Union
+ `star_r_indexed_equiv`: Equivalence of infinite repeat
+ `set_prod_included`: Transitivity of include over product
+ `set_prod_included_left` and `set_prod_included_right`: Specialize `set_prod_included`
+ `set_prod_left/right_nil`: Just like `set_prod_left/right_empty`

And prove correctness for each constructor of general form:
+ `trans_empty`
+ `trans_EmptySet_correct`
+ `trans_EmptyStr_correct`
+ `trans_Optional_correct`
+ `trans_Char_correct`
+ `trans_Concat_correct`
+ `trans_Union_correct`
+ `trans_Plus_correct`
+ `trans_Star_correct`

And we finally get `trans_correct` proven.

To simplify the RegEx, we remove all `EmptyStr` using fixpoint `reduce`. Also we verify its correctness:
+ `reduce_(all constructors of the std form)_correct`
+ `reduce_correct`

Now we use `simpl_p` to feature the simplicity of a reduced RegEx. In the end, we use `trans_reduce_correct` to prove the correctness of `trans` and `reduce`.
