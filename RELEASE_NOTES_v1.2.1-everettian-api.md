# v1.2.1-everettian-api

Corrective release for the Everettian downstream API packaging introduced by
`v1.2.0-everettian-api`.

## Fixes

- The CI aggregate contract no longer imports audit-only leaf modules.
- The four leaf API contracts remain compiled individually.
- The aggregate public-facade smoke contract compiles from a clean checkout.
- Outdated Module C status documentation is corrected to `CLOSED`.
- No scientific declaration, public facade signature, or dependency changed.

`v1.2.1-everettian-api` is the recommended revision for new downstream
consumers. The prior tag `v1.2.0-everettian-api` remains immutable and is not
moved, deleted, or recreated.

This release adds no new mathematical result and performs no downstream
repository migration.