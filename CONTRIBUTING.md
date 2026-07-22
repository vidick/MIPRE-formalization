# Contributing to the MIP* = RE formalization project

Thank you for your interest in contributing to this project!
This guide provides detailed instructions on how to effectively and efficiently contribute to the project. The workflow follows the one pioneered by the [FLT project](https://github.com/ImperialCollegeLondon/FLT).

## Project Coordination

The project is managed using a [GitHub project dashboard](https://github.com/vidick/MIPRE-formalization/projects), which tracks tasks through various stages, from assignment to completion.

## How to Contribute

Contributions to the project are made through GitHub pull requests (PRs) from forks. PRs correspond to specific tasks outlined in the project's issues. The following instructions detail the process for claiming and completing tasks.

### 1. Task Identification

- Tasks are posted as GitHub issues and can be found in the `Unclaimed` column of the project dashboard.
- Each issue represents a specific task to be completed. The issue title and description contain relevant details and requirements, including a link to the corresponding blueprint node.

### 2. Claiming a Task

- To claim a task, comment the single word `claim` on the relevant GitHub issue.
- If no other user is assigned, you will automatically be assigned to the task, and the issue will move to the `Claimed` column.
- If you decide not to work on a task after claiming it, comment the single word `disclaim` on the issue. This will unassign you and return the issue to the `Unclaimed` column, making it available for others to claim.

### 3. Working on the Task

Once you are assigned to an issue, begin working on the corresponding task. You should fork the project and also create a new branch from the `main` branch to develop your solution. Please try and avoid making PRs from `main` as for technical reasons this makes them slightly harder to review.

Before pushing, please check that the project still builds (`lake build`) and, if you added or removed files, that the root import file is up to date (`lake exe mk_all` regenerates it).

If your PR proves a statement that appears in the blueprint, also edit the corresponding environment in the blueprint sources ([`blueprint/src/content/`](blueprint/src/content)): add `\lean{...}` with the full name of the Lean declaration, and `\leanok` to the statement (and to its proof once the proof is `sorry`-free) so that the dependency graph reflects the progress.

### 4. Submitting a Pull Request

- When you are ready to submit your solution, create a PR from the working branch of your fork to the project's `main` branch. Include `Closes #ISSUE_NUMBER` in the PR description so the PR is linked to the task.
- After submitting the PR, comment `propose #PR_NUMBER` on the original issue. This links your PR to the task, and the task will move to the `In Progress` column on the dashboard.
- A task can only move to `In Progress` if it has been claimed by the user proposing the PR.

### 5. Withdrawing or Updating a PR

- If you need to withdraw your PR, comment the single phrase `withdraw #PR_NUMBER` on the issue. The task will return to the `Claimed` column, but you will remain assigned to the issue.
- To submit an updated PR after withdrawal, comment `propose #NEW_PR_NUMBER` following the same process outlined in step 4.

### 6. Review Process

- After finishing the task and ensuring your PR is ready for review, comment `awaiting-review` on the PR. This will add the `awaiting-review` label to your PR and move the task from `In Progress` to the `In Review` column of the dashboard.
- The project maintainers will review the PR. They may request changes, approve the PR, or provide feedback. If they comment `awaiting-author`, this will add the `awaiting-author` label to your PR.
- When you've responded, comment `awaiting-review` again to remove the `awaiting-author` label and add the `awaiting-review` label again.

### 7. Task Completion

- Once the PR is approved and merged, the task will automatically move to the `Completed` column.
- If further adjustments are needed after merging, a new issue will be created to track additional work.

## Style

- Lean code should follow the [Mathlib style guidelines](https://leanprover-community.github.io/contribute/style.html): documentation strings on every definition and theorem, and Mathlib naming conventions.
- General-purpose lemmas that do not mention project-specific definitions belong in the [`MIPRE/Mathlib/`](MIPRE/Mathlib) directory, mirroring Mathlib's own directory structure, so they can be upstreamed.
- Leaving a `sorry` in a merged PR is acceptable **only** if the sorried statement corresponds to a blueprint node that is tracked by an open issue.

## Additional Guidelines and Notes

1. Please adhere to the issue claiming process. If an issue is already assigned to another contributor, refrain from working on it without prior communication with the current claimant. This ensures a collaborative and respectful workflow that values each contributor's efforts.
2. If any part of this workflow does not behave as described (a comment command is ignored, a dashboard card does not move, CI behaves unexpectedly), please open an issue about it — keeping the infrastructure smooth is part of the project.
