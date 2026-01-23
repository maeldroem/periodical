# Workflow

This document describes how the workflow is organized within this repository.

## Principles

- Explicitness: Be explicit on what you want to do, what you have done, etc.
- Transparency: Be transparent with other contributors and coworkers about your work.
- Solidarity: Help others improve, guide them and collaborate with them.

## Version control

### Repository git configuration

This describes how to setup the git configuration, useful for the repository owner.

```sh
git config set core.eol lf # Sets the End-Of-Line to LF
git config set core.autocrlf false # Disables conversion from LF to CRLF
git config set core.editor nano # Instead of vim, use nano, which is more compatible with modern editing habits
```

### User global git configuration

This describes recommended configuration for your git, not only for this repository.
Feel free to replace those recommendations with your own preferences on your machine.

```sh
git config set user.name 'Your name here' # Sets your username (used for commits). Preferably use your GitHub username.
git config set user.email 'my.email@example.com' # Sets your email (used for commits). Preferably use the own linked with your Github account.
git config set init.defaultbranch main # Sets the default branch name to 'main' instead of 'master'
```

Here is a list of aliases that can be useful to shorten your commands.
Edit your `~/.gitconfig` to include the following.

```
[alias]
	c = commit
	sw = switch
	s = status
	cb = branch --show-current
	b = branch
    # Add All
	aa = add -A
	co = checkout
    # l & ls come from https://martin.ankerl.com/2015/12/22/beautiful-git-logs/
	l = log --graph --pretty=format:\"%C(auto)%h%<(3)%d %s %C(bold blue)(%cr, %an)%Creset\" --abbrev-commit --all
	ls = log --graph --pretty=format:\"%C(auto)%h%<(3)%d %s %C(bold blue)(%cr, %an)%Creset%n\" --abbrev-commit --all --find-copies -M --stat
    m = merge --no-ff
    ms = merge --no-ff --squash
	rs = restore
	rb = rebase
	p = push
	pf = push --force-with-lease
	pt = push --tags
    # Creates a branch and switches to it
	swc = switch -c
    # Pushes origin
	po = !"git push --set-upstream origin $(git branch --show-current)"
	# Stashes changes, creates a new branch, switches to it, then pops the stash
	sswc = !sh -c 'git stash && git switch -c $1 && git stash pop' -
	# Stashes changes, switches to a branch, then pops the stash
	ssw = !sh -c 'git stash && git switch $1 && git stash pop' -
	t = tag -a
```

### Commits

Commits should be units representing an increment in your code.
That is to say, they shouldn't be sessions of code, the day you worked, etc.
They should represent a change around a given theme, the committed work should be related.

Moreover, in order to provide clean commits, it is recommended **NOT** to use a single `-m`.
You should either not provide any and edit your commit message and description via the set text editor,
or you should use two `-m` so that you set both the message and description of the commit.

A commit message should be formatted like this:

```
In a **few words**, what your commit is about

Describe in details your commit here, what it is about, why you made such choices etc.
```

Example:

```
Created function for multiplying matrices

Created a function that receives two matrices and multiplies them together.
We needed such a function for speeding up 3D calculations.
In order to make it fast, we used threads to make the function work in parallel.
```

If you insist on using two `-m`, which is discouraged, you would format it like such:

`git commit -m "Created function for multiplying matrices" -m "Created a function that receives two matrices and multiplies them together.\nWe needed such a function for speeding up 3D calculations.\nIn order to make it fast, we used threads to make the function work in parallel."`

If you are writing a merge commit, write about what your whole branch was about, what changes were made etc.

### Branches

There exists two main branches:
- `main`, which is the branch that should remain clean and where commits represent iterations of the project
  (not only new versions, but rather new features, fixes etc.)
- `dev`, where all the development work branches from and where the history of changes is

In order to conserve the history of changes, which is useful for tracking down bugs more efficiently, all branches
merging into `dev` should be merged without Fast-Forward (done by using [the --no-ff option](https://git-scm.com/docs/git-merge#Documentation/git-merge.txt---no-ff)).

This is done in order to conserve ghosts of what the branch was for, therefore explaining the merge.
In order to enforce that, merges from any branch into `dev` should be done by using `git merge --no-ff` and then
following [the commit rules](#commits).

When the `dev` branch has reached a stable state, usually after making sure all tests are passing, it can be merged
into `main`.
This merge should be squashed first so that `main` remains linear and could be extracted as its own product.

To do that, use `git merge --squash --no-ff` and when committing, provide a meaningful message and description, in
accordance to [the commit rules](#commits).

Now, when you start working on a new thing, you should branch off `dev` and should name it by following the syntax
`<type>/<name>`, where `<type>` is the most relevant choice out of the list below, and where `<name>` is
a short name/title for your branch, formatted in lower-case [snake case](https://en.wikipedia.org/wiki/Snake_case).

- `improve`: For features, changes, and other improvements
- `fix`: For bugfixes
- `upgrade`: For dependency upgrades, and perhaps this upgrade needs some code to be upgraded as well.
- `doc`: For documentation
- `test`: For adding/changing tests

The reason that `improve` represents _features, changes, and other improvements_ is that all of those overlap
in a way that makes it hard, sometimes impossible, to clearly separate.

Use `git switch -c` to create and switch to your branch. For example, `git switch -c improve/matrix_multiplication`.

If during your work, or when you have finished working, your branch needs to be up-to-date with `dev`, you should
rebase your branch to `dev` using `git rebase dev <your_branch_name>`.

#### Hotfixes

A hotfix is a fix that needs to be urgently applied to the deployed version of your product.

Hotfix branches should be prefixed by `hotfix`, e.g. `hotfix/cve_2025_53549`.

Those branches branch off `main` and are squash-merged onto `main`.

#### Branch dependencies

Imagine the following scenario: a coworker creates `improve/matrix_maths`, that his branch is not yet merged into `dev`,
and that you would need to branch off it for, let's say, `improve/faster_matrix_multiplication`.

The preferred solution would be to involve features from GitHub's [PR](#pull-requests-prs) system: Your branch branches
off `improve/matrix_maths`, but when creating your PR, you target `dev` instead of `improve/matrix_maths` and
mention the dependency on `improve/matrix_maths` in the PR's description,
citing the PR number of `improve/matrix_maths`, which causes this reference to appear
in the PR for `improve/matrix_maths`.

Then, we wait until `improve/matrix_maths` gets merged into `dev`,
and then use `git rebase --onto dev improve/matrix_maths improve/faster_matrix_multiplication`
before using `git push --force-with-lease`.

Some problems could arise with this solution, see [Recovering From Upstream Rebase](https://git-scm.com/docs/git-rebase#_recovering_from_upstream_rebase).

So this preferred solution is subject to change, and if you figure out a better way to handle this situation,
use it over this suggested solution.

### Pull requests (PRs)

Pull requests should follow [the same rules as commits](#commits): they should be explicit about what they are about, what they
seek to change, etc.

Keep the title short, reserve the description for the details. Use Markdown at your advantage for formatting your
PR description!

See ["Creating a PR" section of CONTRIBUTING.md](CONTRIBUTING.md#creating-a-pr) for more details.

### Tags and releases

Tags should be used to track versions but also milestones. Both milestones and versions are similar in concept, it
just depends on how you define the two.

For version tags, usually they should be named like your version, prefixed with `v` (e.g. `v1.2.3`).
As for milestones, they can be named like `milestone_cool_things_this_time` (`milestone_` being the prefix).

Version tags should generally tag a commit on the `main` branch. As for milestones, either `main` or `dev`.

When creating a tag, use `git tag -a v1.2.3 <commit>` (you can omit `<commit>` if the `HEAD` is already the commit
you wish to tag).
Since we don't provide the `-m` option, this command will open your chosen text editor for you to name the tag.

When naming the tag, follow [the same rules as for commits](#commits): The name/title should be short,
but the description should be explicit, explaining what the tag is about, and if it is for a version or milestone,
should include the changelog for this version/milestone.

Don't forget to use `git push --tags` to push your tags.

Regarding releases, use GitHub's tool for that. Don't forget to detail what your release is about, adding the changelog
and so on. But this time you can use Markdown!

### Versioning scheme

Generally, you should follow [Semantic Versioning 2.0](https://semver.org/spec/v2.0.0.html), unless your project
is subject to change on a regular basis, mainly due to subjects related to time (e.g. laws, timezones, standards,
as they all can change on some interval of time), in which case you should use [Calendar Versioning](https://calver.org/).

Sometimes the choice is ambiguous, sometimes both of those versioning schemes may not fit. It is up to the maintainers
to choose the versioning scheme they choose to use.

## Code

Obviously, you should follow [the code formatting rules](CODE_FORMATTING.md).
But there's also additional rules on coding that you should generally follow.

Warnings should be considered like errors, even if it's a warning with low priority, such as warnings from the
`pedantic` group of lints of `clippy`. Warnings shouldn't be ignored and should be resolved as much as possible.
