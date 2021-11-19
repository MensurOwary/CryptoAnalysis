# CogniCrypt + CrySL

- [ ] IncompleteOperationError only happens when the first used object's last usage is missing. It depends on the variable.

The reason is that AnalysisSeedWithSpecification only tracks one variable, and that variable is the one we check the lifetime of

