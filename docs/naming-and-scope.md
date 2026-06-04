# Naming and Scope

```text
Project name:       Henret
Repository name:    henret
Lake package name:  henret
Lean namespace:     Henret
Subtitle:           Executable actor and task runtime models for Lean 4
```

Henret is a coined name. Public documentation must not rely on etymology;
the subtitle and the examples explain the project.

## Module map

```text
Henret/
  Core/        Id.lean (TaskId, ActorId, upd), Result.lean (StepResult)
  Actor/       Task.lean (TaskState), Mailbox.lean (Message, Mailbox, ActorState)
  Scheduler/   Op.lean (RuntimeOp), Timer.lean, Model.lean (RuntimeState, step, run), Driver.lean
  Proofs/      Lifecycle.lean, Messaging.lean, Timers.lean
  Refinement/  Contract.lean (MailboxBackend), ReferenceBackend.lean
  Examples/    Basic.lean
```

## Terms to avoid in public docs

Do not describe Henret as: "Tokio for Lean", "production async runtime",
"process manager", "native thread library", "fully verified lock-free
scheduler". Reviewers reject changes that blur the actor/task *model* with a
native thread *implementation*.
