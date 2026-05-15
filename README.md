# Thoughts

## Formatting

To check if files are already formatted (useful on CI):

```bash
$ fourmolu --mode check .
```

Find all the source files in a project with `git ls-files` and then use `fourmulu` to format those files:

```bash
$ fourmolu --mode inplace $(git ls-files '*.hs')
# Or to avoid hitting command line length limits and enable parallelism (12-way here):
$ git ls-files -z '*.hs' | xargs -P 12 -0 fourmolu --mode inplace
```
