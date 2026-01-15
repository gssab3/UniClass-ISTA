# Automated Test Plan: UniClass Platform

## 1. Introduction
This document outlines the automation testing strategy for **UniClass**, a Jakarta EE-based platform for university management. The strategy is designed to ensure system dependability, performance, and security by integrating automated suites into the development lifecycle via GitHub Actions.

## 2. Test Objectives
The primary objectives of the automated testing process are:
* **Business Logic Validation**: Ensure that core services (User Management, Scheduling, Messaging) strictly follow defined academic rules.
* **Regression Control**: Prevent new commits from breaking existing functionalities through a mandatory CI pipeline.
* **Performance Benchmarking**: Maintain system responsiveness by measuring throughput and latency of critical components.
* **Security & Compliance**: Automatically detect security flaws, vulnerable dependencies, and leaked secrets.
* **Code Quality Enforcement**: Achieve a minimum code coverage and maintain low technical debt.

## 3. Automation Scope
The automation covers the following layers:
* **Unit Testing**: Individual logic validation of Models, DAOs, and Servlets using JUnit 5 and Mockito.
* **Integration Testing**: Interaction testing between the application logic and the database layer using H2 in-memory DB and Arquillian.
* **Performance Micro-benchmarking**: High-load scenario simulation for messaging and topic retrieval using JMH.
* **Static Analysis**: Automated code smell and bug detection via SonarCloud.
* **Vulnerability Scanning**: Real-time dependency and secret scanning.

## 4. Tools Selection
The automation stack includes:
* **Build & Lifecycle Management**: Apache Maven.
* **Testing Frameworks**: JUnit 5, Mockito, Arquillian.
* **Performance Testing**: Java Microbenchmark Harness (JMH).
* **Code Coverage**: JaCoCo.
* **Security Analysis**: Snyk (SCA) and GitGuardian (Secret Detection).
* **CI/CD Orchestration**: GitHub Actions.

## 5. Test Environment
* **CI Infrastructure**: GitHub Actions Runners (Operating System: Ubuntu-latest).
* **Java Runtime**: JDK 17 (Targeting Jakarta EE 9+).
* **Application Server**: Apache Tomcat 10+ (Docker-ready for local and staging tests).
* **Database**: H2 (In-memory for Unit/Integration tests) and MySQL (for production-ready simulation) as defined in `persistence.xml`.

## 6. Automation Strategy
Automation is fully integrated into the GitHub workflow:
1.  **Triggers**: Workflows are initiated on every `push` and `pull_request` to `master` or `developer` branches.
2.  **Sequential Execution**:
    * **Build**: Compilation of the source code and dependency resolution.
    * **Test Phase**: Execution of JUnit unit and integration tests.
    * **Quality Phase**: JaCoCo generates coverage reports; SonarCloud evaluates the Quality Gate.
    * **Security Phase**: Parallel scans by Snyk and GitGuardian provide a security pass/fail status.
3.  **Performance Check**: Periodic execution of JMH benchmarks to compare results against historical JSON data.

## 7. Testing Schedule
* **Per-Commit**: Unit Tests, Integration Tests, and Static Quality Analysis.
* **Daily/Nightly**: Full dependency security scans and credential checks.
* **Pre-Release**: Manual trigger of Performance Benchmarks to ensure system scalability before production deployment.

## 8. Deliverables
Upon completion of the automated cycles, the following artifacts are produced:
* **JUnit Test Reports**: Detailed logs of all passed/failed test cases.
* **JaCoCo Coverage Report**: HTML mapping of tested code branches.
* **SonarCloud Dashboard**: Live quality metrics and technical debt analysis.
* **Security Audit Summary**: Reports from Snyk and GitGuardian detailing discovered vulnerabilities.
* **JMH Performance Results**: JSON data documenting throughput and execution times for critical services.

## 9. Test Assessment & Evaluation Criterias

### 9.1. Quantitative Metrics (KPIs)
* **Pass Rate**: 100% pass rate for Unit Tests and 95% for Integration Tests required for a "Green" build.
* **Code Coverage**: Total coverage must exceed the project baseline (e.g., 80%).
* **Technical Debt**: Evaluated via SonarCloud; must maintain a Rating A (Debt Ratio < 5%).

### 9.2. Quality Gates (Go/No-Go Criteria)
The Assessment phase implements automated Quality Gates. A "Fail" status in any of the following will block the build:

* **Security Blockers**: Any "Critical" or "High" severity vulnerability identified by **Snyk** or leaked credentials detected by **GitGuardian**.
* **Static Analysis Standard**: The project must comply with the **SonarWay** Quality Gate. Code that does not meet "Clean Code" standards will be rejected.
* **Reliability Core**: Failure of core dependability tests (e.g., Login, Security Filters) is a non-negotiable blocker.

#### 9.2.1. Multi-Stage Code Review Strategy
UniClass adopts a three-tiered analysis approach using SonarQube to ensure **Correctness by Construction**:

1.  **IDE Layer (Local Analysis)**: Developers fix issues as they are introduced using SonarLint. This "Shift-Left" approach ensures correctness before code is committed.
2.  **Pull Request Layer (Merge Guard)**: Automated analysis for every PR acts as a gatekeeper, ensuring only clean code is merged.
3.  **Branch Layer (Release Readiness)**: Full analysis of main branches ensures the system is stable and ready for deployment.


### 9.3. Result Interpretation & Documentation
* **Failure Analysis**: In case of automated test failure, the logs from GitHub Actions are manually analyzed.
* **Baseline Comparison**: Performance results are compared against 
data to verify that modularity is not impacting system responsiveness.
* **Final Assessment Report**: A summary of the security scans and coverage is aggregated into the `SecurityWorkflow-report.md` for stakeholders review.

### 9.4. Feedback Loop
* **Issue Tracking**: Every failed assessment must result in an automatically generated GitHub Issue or a blocked Pull Request until the fix is verified by a new CI run.
* **Continuous Improvement**: Test cases that fail frequently due to flakiness (e.g., database timeout) are reviewed and the `wait-for-it.sh` or mocking strategy is adjusted.
