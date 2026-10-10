# grammar-store

A generic store for expert-system-style interactions in Lean 4, with English past tense as the first domain.

## Layout

| File | Contents | Domain-specific? |
|---|---|---|
| `GrammarStore/Prog.lean` | Rules as programs over a query interface; `run`, `trace`; `run_congr`, `trace_congr` | no |
| `GrammarStore/Store.lean` | `Domain`, layered `KB`, `Entry` (answer + trace), `Session` with `ask` / `rebase` / `push` / `pop`; coherence theorems | no |
| `GrammarStore/English/Morphology.lean` | Principal parts, weak-past spelling, tokens | yes, pure |
| `GrammarStore/English/Domain.lean` | Queries, layers, oracle, rule programs, the `english` domain, domain theorems, kernel-checked examples, `#eval demo` | yes |
| `Main.lean` | Line-protocol server (`.` terminates each response) | yes |
| `serve.py` | HTTP front: `curl -d 'check She teached us.' localhost:8080` | no |

## What is proved once, for every domain

- `Prog.run_congr`, `Prog.trace_congr`: an answer and its trace depend only on the questions asked.
- `Entry.record_eq`: an entry whose trace agrees with a new knowledge base *is* that knowledge base's entry.
- `Session.init_coherent`, `ask_coherent`, `rebase_coherent` (hence `push_coherent`, `pop_coherent`): the cache never holds a stale entry.
- `Session.ask_correct`, `ask_holds`: every served answer equals recomputation against the current knowledge base.

## What a domain owes

- A keyed query type `Q` with answer types `A q`. Invalidation is exactly as local as the queries are keyed; a scan over the whole lexicon belongs in a derived index such as `readings`.
- A layer type and `answer : List Layer → (q : Q) → A q`. Override, retraction and indexes are the domain's business.
- Goal programs in `Prog`, plus whatever domain theorems are wanted (here `run_formOf`, `past_eq_pp_of_regular`, `formOf_absent`, `PastOf.unique`).

## Known limits

- Ambiguous words: a sentence answer carries one label covering all readings, so the label is sound but coarser than per-reading. Per-reading labels need a `choose` constructor in `Prog` and a list-valued `run`, which is the next step.
- `switch` merges two coherent caches over the same knowledge base. That is obviously coherent, but not yet stated as a theorem.
- Nothing stops domain code from reading the layers directly and bypassing tracking. Put domains in separate modules that see only `Prog` and the oracle.

## Build

```
lake build
lake exe grammar-store      # or: python3 serve.py
```
