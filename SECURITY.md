# Security policy

## Supported versions

| Version | Supported |
| --- | --- |
| 0.1.x | yes |

There are no older releases. `0.x` is a development series. See `CHANGELOG.md`.

## Reporting a vulnerability

Report vulnerabilities privately through a
[GitHub security advisory](https://github.com/kidandcat/cairn/security/advisories/new)
on this repository.

Do not open a public issue for a vulnerability, and do not put exploit
details in a pull request.

Include the version or commit, how to reproduce the problem, and the impact
you saw. A crash that keeps a prefix of a well-formed log is the stated
failure model, not by itself a vulnerability. A case that acknowledges a
commit whose bytes did not reach the barrier, or that accepts a frame the
checksum should have rejected, is.

There is no bug-bounty program. The maintainers will acknowledge the
advisory and use it to coordinate a fix.
