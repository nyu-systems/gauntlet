# Bug Breakdown

This folder is an archive of all the bugs we have found and file while using Gauntlet. The following folder structure explains the meaning of the individual categories. Every folder also contains a `fixed` and `denied` folders. Bugs that have been fixed or denied by the maintainers are filed there. Bugs in the top-level directory are confirmed and open.

```
bugs
├── crash                   -- Crash bugs found in P4C. File numbers correspond to issues filed in https://github.com/p4lang/p4c/issues.
├── improvements            -- Issues that were considered "enhancements" by the compiler maintainers.  File numbers correspond to issues filed in https://github.com/p4lang/p4c/issues.
├── invalid_transformation  -- These are IR transformation that did not lead to a compiler bug but violated the invariant that the compiler IR must be valid at all times during compilation.
├── simple_switch           -- Bugs found in the simple switch software when running an stf test. File numbers correspond to issues filed in https://github.com/p4lang/behavioral-model/issues.
├── spec                    -- Specification issues that were uncovered when asking questions or filing bug reports. Numbers correspond to issues raised at https://github.com/p4lang/p4-spec/issues.
├── tofino                  -- Bugs found in the compiler for the Tofino chip. More precisely for the tna.p4 package. We can only discuss the bugs we found and the type of the bug.
│   ├── crash               -- Simple compiler crashes.
│   ├── missing_pass        -- Crashes found in bf-p4c that were caused by the P4C front end not transforming passes correctly.
│   └── semantic            -- Semantic bugs that were uncovered using model-based testing using PTF and test packets.
└── validation              -- Semantics bugs that were uncovered in P4C using translation validation. The majority of bugs were also reproduced using model-based testing and an STF file is supplied with the bug.
```


### Bug Tables
Last Updated: 2022-06-14

The bug tables provide the latest, detailed breakdown of all the issues we have filed in the open-source repositories.

Legend:

Fixed: :heavy_check_mark:&nbsp;&nbsp;&nbsp;&nbsp;Confirmed: :exclamation:&nbsp;&nbsp;&nbsp;&nbsp;Denied: :no_entry:&nbsp;&nbsp;&nbsp;&nbsp;Open: :question:


#### P4C Crash Bugs

| Issue                                                        | Location                    | Compiler Stage | Status    |
| ------------------------------------------------------------ | --------------------------- | -------------- | --------- |
| [Compiler Bug: visitor returned non-Statement type (2102)](https://github.com/p4lang/p4c/issues/2102)            | [2102.p4](crash/fixed/2102.p4)         | Mid end | :heavy_check_mark: |
| [Compiler Bug: no definitions (2104)](https://github.com/p4lang/p4c/issues/2104)            | [2104a.p4](crash/fixed/2104a.p4)       | Front end | :heavy_check_mark: |
| [Compiler Bug: no definitions (2104)](https://github.com/p4lang/p4c/issues/2104)            | [2104b.p4](crash/fixed/2104b.p4)       | Front end | :heavy_check_mark: |
| [Compiler Bug: no locations known for <Mux> (2105)](https://github.com/p4lang/p4c/issues/2105)            | [2105.p4](crash/fixed/2105.p4)         | Front end | :heavy_check_mark: |
| [InlineFunctions pass sometime seems to generate invalid code. (2126)](https://github.com/p4lang/p4c/issues/2126)            | [2126.p4](crash/fixed/2126.p4)         | Front end | :heavy_check_mark: |
| [p4c-bm2-ss crashes on undefined header conditional in method (2148)](https://github.com/p4lang/p4c/issues/2148)            | [2148.p4](crash/fixed/2148.p4)         | Mid end | :heavy_check_mark: |
| [Follow-up to issue 2104, exit also kills all variables (2151)](https://github.com/p4lang/p4c/issues/2151)            | [2151.p4](crash/fixed/2151.p4)         | Front end | :heavy_check_mark: |
| [Compiler Bug: At this point in the compilation typechecking should not infer new types anymore, but it did. (2190)](https://github.com/p4lang/p4c/issues/2190)            | [2190.p4](crash/fixed/2190.p4)         | Front end | :heavy_check_mark: |
| [Compiler Bug: Null cst (2206)](https://github.com/p4lang/p4c/issues/2206)            | [2206.p4](crash/fixed/2206.p4)         | Front end | :heavy_check_mark: |
| [Compiler Bug: boost::too_few_args (2207)](https://github.com/p4lang/p4c/issues/2207)            | [2207.p4](crash/denied/2207.p4)       | Front end | :no_entry:    |
| [Predication pass leads to unsafe variable assignment (2248c)](https://github.com/p4lang/p4c/issues/2248)           | [2248c.p4](crash/fixed/2248c.p4)       | Mid end | :heavy_check_mark: |
| [Compiler Bug: Null stat (2258a)](https://github.com/p4lang/p4c/issues/2258)            | [2258a.p4](crash/fixed/2258a.p4)                  | Front end | :heavy_check_mark: |
| ["error: Duplicates declaration" when initializing struct in function with integer values (2261)](https://github.com/p4lang/p4c/issues/2261)            | [2261.p4](crash/fixed/2261.p4)         | Front end | :heavy_check_mark: |
| ["Compiler Bug Null stat" also triggered in action properties (2266)](https://github.com/p4lang/p4c/issues/2266)            | [2266.p4](crash/fixed/2266.p4)                     | Front end | :heavy_check_mark: |
| [Compiler Bug: visitor returned invalid type Vector<Declaration> for IndexedVector<StatOrDecl> (2289)](https://github.com/p4lang/p4c/issues/2289)            | [2289.p4](crash/fixed/2289.p4)         | Mid end | :heavy_check_mark: |
| [Compiler Bug: Unexpected type <Type_Name> for nested headers (2290)](https://github.com/p4lang/p4c/issues/2290)            | [2290.p4](crash/fixed/2290.p4)         | Front end | :heavy_check_mark: |
| [BMV2 Backend Compiler Bug unhandled case (2291)](https://github.com/p4lang/p4c/issues/2291)            | [2291.p4](crash/fixed/2291.p4)         | Back end | :heavy_check_mark: |
| [Compiler Bug: Could not find type of @name (2336)](https://github.com/p4lang/p4c/issues/2336)            | [2336.p4](crash/fixed/2336.p4)         | Front end | :heavy_check_mark: |
| [Compile-time-known and slices (2342)](https://github.com/p4lang/p4c/issues/2342)            | [2342.p4](crash/fixed/2342.p4)         | Front end | :heavy_check_mark: |
| [Compiler Bug: Null cst for InfInt Parameters (2354)](https://github.com/p4lang/p4c/issues/2354)            | [2354.p4](crash/fixed/2354.p4)         | Front end | :heavy_check_mark: |
| [Silent crash: Struct Parameters (2355)](https://github.com/p4lang/p4c/issues/2355)            | [2355.p4](crash/fixed/2355.p4)         | Front end | :heavy_check_mark: |
| [Negative bit index in Slice after shifting function output (2356)](https://github.com/p4lang/p4c/issues/2356)            | [2356.p4](crash/fixed/2356.p4)         | Front end | :heavy_check_mark: |
| [Int as parameter and assignments (2357)](https://github.com/p4lang/p4c/issues/2357)            | [2357.p4](crash/fixed/2357.p4)         | Front end | :heavy_check_mark: |
| [Mixing exits and returns in actions (2359)](https://github.com/p4lang/p4c/issues/2359)            | [2359.p4](crash/fixed/2359.p4)         | Mid end | :heavy_check_mark: |
| [Another expression with side-effects in table keys and actions (2362)](https://github.com/p4lang/p4c/issues/2362)            | [2362.p4](crash/fixed/2362.p4)                     | Front end | :heavy_check_mark: |
| [No Definitions in Parser Loop (2373)](https://github.com/p4lang/p4c/issues/2373)            | [2373.p4](crash/fixed/2373.p4)         | Front end | :heavy_check_mark: |
| [Crash when running end-to-end tests with simple switch (2375)](https://github.com/p4lang/p4c/issues/2375)            | [2375.p4](crash/fixed/2375.p4)         | Back end | :heavy_check_mark: |
| [Compiler Bug: no definitions (2393)](https://github.com/p4lang/p4c/issues/2393)            | [2393.p4](crash/fixed/2393.p4)                     | Front end | :heavy_check_mark: |
| [p4test: x: declaration not found (2435a)](https://github.com/p4lang/p4c/issues/2435)            | [2435a.p4](crash/fixed/2435a.p4)      | Mid end | :heavy_check_mark: |
| [Range starting from zero: Can not shift by a negative value (2485)](https://github.com/p4lang/p4c/issues/2485)            | [2485.p4](crash/fixed/2485.p4)         | Mid end | :heavy_check_mark: |
| [Conditional execution in actions with struct initializers (2486)](https://github.com/p4lang/p4c/issues/2486)            | [2486.p4](crash/denied/2486.p4)       | Mid end | :no_entry:    |
| [StructInitializer in Mux expressions (2487)](https://github.com/p4lang/p4c/issues/2487)            | [2487.p4](crash/fixed/2487.p4)         | Mid end | :heavy_check_mark: |
| [p4c-bm2-ss: Compiler Bug: Could not convert to Json (2495)](https://github.com/p4lang/p4c/issues/2495)            | [2495.p4](crash/fixed/2495.p4)         | Back end | :heavy_check_mark: |
| [Control Inlining: Key declaration not found (2542)](https://github.com/p4lang/p4c/issues/2542)            | [2542.p4](crash/denied/2542.p4)       | Front end | :no_entry:    |
| [Some problems with function calls in struct initialization (2543a)](https://github.com/p4lang/p4c/issues/2543)           | [2543a.p4](crash/fixed/2543a.p4)       | Mid end | :heavy_check_mark: |
| [Some problems with function calls in struct initialization (2543b)](https://github.com/p4lang/p4c/issues/2543)           | [2543b.p4](crash/fixed/2543b.p4)       | Front end | :heavy_check_mark: |
| [Compiler Bug: Could not find type of <Declaration_Variable> for declaration of same name (2544)](https://github.com/p4lang/p4c/issues/2544)            | [2544.p4](crash/fixed/2544.p4)                     | Front end | :heavy_check_mark: |
| [Calling an extern with a local variable: read-only error (2545)](https://github.com/p4lang/p4c/issues/2545)            | [2545.p4](crash/fixed/2545.p4)         | Mid end | :heavy_check_mark: |
| [Side-effect function call in table key (2546b)](https://github.com/p4lang/p4c/issues/2546)           | [2546b.p4](crash/fixed/2546b.p4)                   | Front end | :heavy_check_mark: |
| [Compiler Bug : Null firstCall (2597)](https://github.com/p4lang/p4c/issues/2597)           | [2597.p4](crash/fixed/2597.p4)                   | Front end | :heavy_check_mark: |
| [Compiler Bug: Exiting with SIGSEGV (2648)](https://github.com/p4lang/p4c/issues/2648)           | [2648.p4](crash/fixed/2648.p4)                   | Mid end | :heavy_check_mark: |
| [simple_switch died with return code -6 (887)](https://github.com/p4lang/behavioral-model/issues/887) | [887.p4](simple_switch/fixed/887.p4) | Back end | :heavy_check_mark: |

#### P4C Semantic Bugs

| Issue                                                        | Location                    | Compiler Stage | Status    |
| ------------------------------------------------------------ | --------------------------- | -------------- | --------- |
| [SimplifyDefUse incorrectly removes assignment in actions with slices as arguments (2147)](https://github.com/p4lang/p4c/issues/2147)            | [2147.p4](validation/fixed/2147.p4)    | Front end | :heavy_check_mark: |
| [Switchstatement: Assignment in switch-case removed (2153)](https://github.com/p4lang/p4c/issues/2153)            | [2153.p4](validation/fixed/2153.p4)    | Mid end | :heavy_check_mark: |
| [Question about parser behavior with right shifts (2156)](https://github.com/p4lang/p4c/issues/2156)            | [2156.p4](validation/fixed/2156.p4)    | Front end | :heavy_check_mark: |
| [Associative order of shift operators (2161)](https://github.com/p4lang/p4c/issues/2161)            | [2161.p4](validation/fixed/2161.p4)    | Back end | :heavy_check_mark: |
| [RemoveReturns deletes return in SwitchStatements (2170)](https://github.com/p4lang/p4c/issues/2170)            | [2170.p4](validation/fixed/2170.p4)    | Mid end | :heavy_check_mark: |
| [Assignment removed despite conditional return (2175)](https://github.com/p4lang/p4c/issues/2175)            | [2175.p4](validation/fixed/2175.p4)    | Front end | :heavy_check_mark: |
| [Question on precise behavior of copy-out (2176)](https://github.com/p4lang/p4c/issues/2176)            | [2176.p4](validation/fixed/2176.p4)    | Front end | :heavy_check_mark: |
| [Compiler Bug: At this point in the compilation typechecking should not infer new types anymore, but it did. (2190)](https://github.com/p4lang/p4c/issues/2190)            | [2190a.p4](validation/fixed/2190a.p4)  | Front end | :heavy_check_mark: |
| [Question on side-effect ordering (2205)](https://github.com/p4lang/p4c/issues/2205)            | [2205.p4](validation/fixed/2205.p4)    | Front end | :heavy_check_mark: |
| [Clarification question on setInvalid (2212)](https://github.com/p4lang/p4c/issues/2212)            | [2212.p4](validation/denied/2212.p4)  | Front end | :no_entry:    |
| [StrengthReduction ignores side-effects in function calls (2221)](https://github.com/p4lang/p4c/issues/2221)            | [2221.p4](validation/fixed/2221.p4)    | Front end | :heavy_check_mark: |
| [Calling exit in actions after an assignment (2225)](https://github.com/p4lang/p4c/issues/2225)            | [2225.p4](validation/fixed/2225.p4)    | Mid end | :heavy_check_mark: |
| [Predication pass leads to unsafe variable assignment (2248a)](https://github.com/p4lang/p4c/issues/2248)           | [2248a.p4](validation/fixed/2248a.p4)  | Mid end | :heavy_check_mark: |
| [Predication pass leads to unsafe variable assignment (2248b)](https://github.com/p4lang/p4c/issues/2248)           | [2248b.p4](validation/fixed/2248b.p4)  | Mid end | :heavy_check_mark: |
| [Missed side-effect case StrengthReduction (2287)](https://github.com/p4lang/p4c/issues/2287)            | [2287.p4](validation/fixed/2287.p4)    | Front end | :heavy_check_mark: |
| [SideEffectOrdering: Regression? (2288a)](https://github.com/p4lang/p4c/issues/2288)            | [2288a.p4](validation/fixed/2288a.p4)    | Front end | :heavy_check_mark: |
| [SideEffectOrdering: Regression? (2288b)](https://github.com/p4lang/p4c/issues/2288)            | [2288b.p4](validation/fixed/2288b.p4)    | Front end | :heavy_check_mark: |
| [MoveInitializers and parser loops (2314)](https://github.com/p4lang/p4c/issues/2314)            | [2314.p4](validation/fixed/2314.p4)    | Front end | :heavy_check_mark: |
| [More questions on setInvalid (2323)](https://github.com/p4lang/p4c/issues/2323)            | [2323.p4](validation/denied/2323.p4)  | Front end | :no_entry:    |
| [Another issue with Predication (2330)](https://github.com/p4lang/p4c/issues/2330)            | [2330.p4](validation/fixed/2330.p4)    | Mid end | :heavy_check_mark: |
| [Another missed case of StrengthReduction (2343)](https://github.com/p4lang/p4c/issues/2343)            | [2343.p4](validation/fixed/2343.p4)    | Front end | :heavy_check_mark: |
| [Inlining functions and duplicate table calls (2344)](https://github.com/p4lang/p4c/issues/2344)            | [2344.p4](validation/fixed/2344.p4)                | Mid end | :heavy_check_mark: |
| [Incorrect transformation in Predication pass (2345b)](https://github.com/p4lang/p4c/issues/2345)           | [2345b.p4](validation/fixed/2345b.p4)  | Mid end | :heavy_check_mark: |
| [Follow-up issue on exit statements (2358a)](https://github.com/p4lang/p4c/issues/2358)           | [2358a.p4](validation/fixed/2358a.p4)              | Front end | :heavy_check_mark: |
| [Follow-up issue on exit statements (2358b)](https://github.com/p4lang/p4c/issues/2358)           | [2358b.p4](validation/fixed/2358b.p4)              | Front end | :heavy_check_mark: |
| [Def-Use and exit statements (2374)](https://github.com/p4lang/p4c/issues/2374)            | [2374.p4](validation/denied/2374.p4)  | Front end | :no_entry:    |
| [InlineActions also seems to handle exit statements incorrectly (2382)](https://github.com/p4lang/p4c/issues/2382)            | [2382.p4](validation/denied/2382.p4)  | Front end | :no_entry:    |
| [Clarification question on uninitialized local headers (2383)](https://github.com/p4lang/p4c/issues/2383)            | [2383.p4](validation/fixed/2383.p4)    | Mid end | :heavy_check_mark: |
| [Question on comparison to negative constants (2392)](https://github.com/p4lang/p4c/issues/2392)            | [2392.p4](validation/fixed/2392.p4)    | Front end | :heavy_check_mark: |
| [Inlining controls with out parameters (2470)](https://github.com/p4lang/p4c/issues/2470)            | [2470.p4](validation/denied/2470.p4)  | Front end | :no_entry:    |
| [Side effects in StructInitializers (2488)](https://github.com/p4lang/p4c/issues/2488)            | [2488.p4](validation/fixed/2488.p4)    | Front end | :heavy_check_mark: |
| [Follow-up on slice arguments (2498)](https://github.com/p4lang/p4c/issues/2498)            | [2498.p4](validation/fixed/2498.p4)                | Front end | :heavy_check_mark: |
| [Side-effect function call in table key (2546b)](https://github.com/p4lang/p4c/issues/2546)           | [2546b.p4](validation/fixed/2546b.p4)              | Mid end | :heavy_check_mark: |
| [Fix: Predication issue (2564)](https://github.com/p4lang/p4c/pull/2564)              | [2564.p4](validation/pull_request/2564.p4)  | Mid end | :heavy_check_mark: |
| [Fix: Issue #2004 parser duplicated matches not optimized out (2591)](https://github.com/p4lang/p4c/pull/2591)              | [2591.p4](validation/pull_request/2591.p4)  | Mid end | :heavy_check_mark: |
| [Predication: Another problem (2613)](https://github.com/p4lang/p4c/issues/2613)              | [2564.p4](validation/fixed/2613.p4)  | Mid end | :heavy_check_mark: |
| :tada: (Bug No 100!) [StrengthReduction: Incorrect slice optimization (2614)](https://github.com/p4lang/p4c/issues/2614)              | [2614.p4](validation/fixed/2614.p4)  | Front end | :heavy_check_mark: |
| [Some more predication issues (2647)](https://github.com/p4lang/p4c/issues/2647)              | [2647a.p4](validation/fixed/2647a.p4)  | Mid end | :heavy_check_mark: |

#### Tofino Crash Bugs (P4Studio 9.9.0)

| Issue                                                        | Name                    | Compiler Stage | Status    |
| ------------------------------------------------------------ | --------------------------- | -------------- | --------- |
| 1                                                            | [bug1.p4](tofino/crash/denied/bug1.p4)       | Front end | :no_entry:    |
| 2                                                            | [bug2.p4](tofino/crash/denied/bug2.p4)       | Front end | :no_entry:    |
| 3                                                            | [bug3.p4](tofino/missing_pass/bug3.p4)       | Back end | Front end issue |
| 4                                                            | [bug4.p4](tofino/crash/denied/bug4.p4)       | Front end | :no_entry:    |
| 5                                                            | [bug5.p4](tofino/crash/bug5.p4)              | Back end | :heavy_check_mark: |
| 6                                                            | [bug6.p4](tofino/crash/bug6.p4)              | Back end | :heavy_check_mark: |
| 7                                                            | [bug7.p4](tofino/crash/bug7.p4)              | Back end | :heavy_check_mark: |
| 8                                                            | [bug8.p4](tofino/crash/bug8.p4)              | Back end | :heavy_check_mark: |
| 9                                                            | [bug9.p4](tofino/crash/bug9.p4)              | Back end | :heavy_check_mark: |
| 10                                                           | [bug10.p4](tofino/crash/bug10.p4)            | Back end | :heavy_check_mark: |
| 11                                                           | [bug11.p4](tofino/crash/bug11.p4)            | Back end | :heavy_check_mark: |
| 12                                                           | [bug12.p4](tofino/crash/bug12.p4)            | Back end | :exclamation_mark: |
| 13                                                           | [bug13.p4](tofino/missing_pass/bug13.p4)     | Back end | Front end issue |
| 14                                                           | [bug14.p4](tofino/crash/bug14.p4)            | Back end | :heavy_check_mark: |
| 15                                                           | [bug15.p4](tofino/crash/bug15.p4)            | Back end | :heavy_check_mark: |
| 16                                                           | [bug16.p4](tofino/crash/bug16.p4)            | Back end | :heavy_check_mark: |
| 17                                                           | [bug17.p4](tofino/crash/bug17.p4)            | Back end | :exclamation: |
| 18                                                           | [bug18.p4](tofino/crash/bug18.p4)            | Back end | :heavy_check_mark: |
| 19                                                           | [bug19.p4](tofino/crash/bug19.p4)            | Back end | :heavy_check_mark: |
| 20                                                           | [bug20.p4](tofino/crash/bug20.p4)            | Back end | :heavy_check_mark: |
| 21                                                           | [bug21.p4](tofino/crash/bug21.p4)            | Back end | :heavy_check_mark: |
| 22                                                           | [bug22.p4](tofino/crash/bug22.p4)            | Back end | :exclamation: |
| 23                                                           | [bug23.p4](tofino/crash/bug23.p4)            | Back end | :exclamation: |
| 24                                                           | [bug24.p4](tofino/crash/bug24.p4)            | Back end | :heavy_check_mark: |
| 25                                                           | [bug25.p4](tofino/crash/bug25.p4)            | Back end | :heavy_check_mark: |
| 26                                                           | [bug26.p4](tofino/crash/bug26.p4)            | Back end | :exclamation: |
| 27                                                           | [bug27.p4](tofino/missing_pass/bug27.p4)     | Back end | Front end issue |
| 28                                                           | [bug28.p4](tofino/crash/denied/bug28.p4)     | Back end | :no_entry:    |
| 29                                                           | [bug29.p4](tofino/missing_pass/bug29.p4)     | Back end | Front end issue |
| 30                                                           | [bug30.p4](tofino/crash/bug30.p4)            | Back end | :heavy_check_mark: |
| 31                                                           | [bug31.p4](tofino/crash/bug31.p4)            | Back end | :heavy_check_mark: |
| 32                                                           | [bug32.p4](tofino/crash/denied/bug32.p4)     | Back end | :no_entry:    |
| 33                                                           | [bug33.p4](tofino/crash/bug33.p4)            | Back end | :heavy_check_mark: |
| 34                                                           | [bug34.p4](tofino/missing_pass/bug34.p4)     | Back end | Front end issue  |
| 35                                                           | [bug35.p4](tofino/crash/bug35.p4)            | Back end | :heavy_check_mark: |

#### Tofino Semantic Bugs (P4Studio 9.9.0)

| Issue                                                        | Name                    | Compiler Stage | Status    |
| ------------------------------------------------------------ | --------------------------- | -------------- | --------- |
| 1                                                            | [semantic_bug1.p4](tofino/semantic/semantic_bug1.p4)           | Back end | :heavy_check_mark: |
| 2                                                            | [semantic_bug2.p4](tofino/semantic/fixed/semantic_bug2.p4)           | Back end | :heavy_check_mark: |
| 3                                                            | [semantic_bug3.p4](tofino/semantic/semantic_bug3.p4)           | Back end | :heavy_check_mark: |
| 4                                                            | [semantic_bug4.p4](tofino/semantic/fixed/semantic_bug4.p4)           | Back end | :heavy_check_mark: |
| 5                                                            | [semantic_bug5.p4](tofino/semantic/fixed/semantic_bug5.p4)           | Back end | :heavy_check_mark: |
| 6                                                            | [semantic_bug6.p4](tofino/semantic/denied/semantic_bug6.p4)    | Back end | :no_entry:    |
| 7                                                            | [semantic_bug7.p4](tofino/semantic/fixed/semantic_bug7.p4)           | Back end | :heavy_check_mark: |
| 8                                                            | [semantic_bug8.p4](tofino/semantic/fixed/semantic_bug8.p4)           | Back end | :heavy_check_mark: |
| 9                                                            | [semantic_bug9.p4](tofino/semantic/denied/semantic_bug9.p4)    | Back end | :no_entry:    |
| 10                                                           | [semantic_bug10.p4](tofino/semantic/denied/semantic_bug10.p4)  | Back end | :no_entry:    |
