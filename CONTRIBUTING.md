# Contributing to `periodical`

Thank you for your interest in contributing to `periodical`! There are many ways to contribute and we appreciate
all of them.

<!-- The best way to get started is by asking for help in `PUT DEDICATED CHANNEL HERE`. -->

You can also get started on your own by creating a Pull Request (PR) or reporting a bug!
Use the [crate's documentation](https://docs.rs/periodical) at your advantage.

## Creating a PR

If one issue caught your eye if you have an idea on how you can add something to the code, please create a pull request!

If it is based on an existing issue, please refer to the issue number in the PR anywhere in the description or title.

Keep your PR title short! If it GitHub is forced to put an ellipsis (...) for your title, then it's probably too long.

Explain what you changed or plan to change in your PR description!
Also provide [a changelog](https://keepachangelog.com/en/1.1.0/) of what you did.

Here's an example of what your PR should look like:

```md
Title: Improved structure for game controllers, added flexibility

Description:

# Explanation

This addresses issues #90123, #89762, and #951.

The structure for how we handled game controllers is not flexible enough and has an outdated structure, this PR
seeks to improve how we handle them, as well as adding traits for easier third-party implementations.

For example, our way of handling PS3 controllers was hard-coded into a single structure that didn't fit with the rest,
this PR changes that and makes every controller fit neatly with proper trait implementations and new-types.

# Changelog

## Added

- `ButtonPress` trait
- `BluetoothConnectable` trait

## Changed

- `PS3GameController` structure to be replaced with a variant in enum `ControllerType`: `PlayStation(3)`.
- Display values for the `ControllerType` enum.
```

## Suggestions

Please create an issue marked with the tag used for suggestions! Make sure that your suggestion wasn't already
addressed first though.

Be as descriptive as you can. Ideally your suggestion should include:

- The general idea
- Use case (how a user would use such feature and what they would achieve with it)
- How this could be implemented
- Approximation of the priority (and why such priority?)
- If available, related feedbacks from users that this suggestion would seek to address

## Reporting a bug

Please create an issue marked with the relevant tags. Make sure that an issue for the same bug doesn't already
exist first.

Be as descriptive as you can. Ideally your bug report should include:

- How to reproduce the bug (including hardware info if it is hardware-dependent)
- The severity of the bug
- If possible, what you think is causing this and/or how you think it should be fixed
- If available, related feedbacks from users that have encountered the bug

## Code formatting

See [the CODE_FORMATTING file](CODE_FORMATTING.md).

## Workflow

See [the WORKFLOW file](WORKFLOW.md).
