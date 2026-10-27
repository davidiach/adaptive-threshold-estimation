# Failed acceptance harness attempt

The first execution of check_checkpoint.py exited1 before writing ACCEPTANCE.json or the post-proof manifest. At line43 it treated the small-bias arithmetic record's boolean values as dictionaries, raising `TypeError: 'bool' object is not subscriptable`. The single-coin record uses dictionaries with a `passed` field, while the small-bias record uses literal booleans.

The new harness was corrected to test each documented schema exactly (`passed is True` or `value is True`). No mathematical proof, stored diagnostic result, old validator, acceptance criterion, or freeze manifest changed. This was a packaging-script error, not a passing check and not evidence against the mathematical statement. The corrected invocation is recorded separately in ACCEPTANCE.json.
