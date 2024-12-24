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