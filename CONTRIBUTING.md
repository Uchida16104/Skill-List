# Contributing to Skill List

Thank you for your interest in contributing to the Skill List project!

## Development Process

1. Fork the repository
2. Create a feature branch (`git checkout -b feature/amazing-feature`)
3. Make your changes
4. Run verification: `./scripts/verify_spec.sh`
5. Compile artifacts: `./scripts/compile_all.sh`
6. Test locally
7. Commit your changes (`git commit -m 'Add amazing feature'`)
8. Push to the branch (`git push origin feature/amazing-feature`)
9. Open a Pull Request

## Code Standards

- All F* and Dafny code must verify successfully
- Rust code must pass `cargo clippy` and `cargo test`
- TypeScript code must pass `npm run lint`
- Follow existing code style and conventions

## Reporting Issues

Please use GitHub Issues to report bugs or request features.

## Questions?

Open a discussion on GitHub or contact the maintainers.
