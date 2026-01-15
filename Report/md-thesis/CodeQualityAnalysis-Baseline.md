# Initial Quality & Security Assessment  
## SonarCloud Static Analysis – Baseline Report

---

## 1. Context and Scope

This document presents the initial baseline assessment of the project’s quality, security, and reliability, conducted through a static analysis using SonarCloud.  
The goal of this phase is not immediate remediation, but a precise understanding of the starting condition of the codebase in terms of risk exposure and quality attributes.

The analysis focuses on identifying the types of issues present, their severity, the quality dimensions most affected, and the areas that require immediate attention.  
All results are derived from two SonarCloud issue reports (`issuesSonar.json`, `issuesSonar2.json`) and represent the state of the system prior to any corrective intervention.

---

## 2. Global Overview of Detected Issues

The static analysis identified a total of **882 issues** across the analyzed codebase.  
These issues are distributed across multiple severity levels and categories, providing a comprehensive overview of the system’s initial risk profile.

### 2.1 Severity Distribution

| Severity | Number of Issues |
|--------|------------------|
| BLOCKER | 17 |
| CRITICAL | 278 |
| MAJOR | 294 |
| MINOR | 293 |
| **Total** | **882** |

From a risk-oriented perspective, the **295 BLOCKER and CRITICAL issues** represent an immediate threat to system security, correctness, and operational stability.

pie title Severity Distribution
    "BLOCKER" : 17
    "CRITICAL" : 278
    "MAJOR" : 294
    "MINOR" : 293


| Issue Type    | Number of Issues |
| ------------- | ---------------- |
| BUG           | 312              |
| VULNERABILITY | 42               |
| CODE_SMELL    | 528              |

Although Code Smells constitute the largest group numerically, the analysis deliberately prioritizes Bugs and Vulnerabilities due to their direct impact on system dependability. Maintainability concerns are therefore considered secondary at this stage.

The following diagram highlights the relationship between issue types and severity levels.



This representation shows that Bugs span the entire severity spectrum, while Vulnerabilities are concentrated in higher severity levels, confirming their critical security relevance.

## 3. Security and Reliability Perspective
### 3.1 Security: Vulnerabilities

The analysis detected 42 Vulnerabilities, explicitly classified by SonarCloud as security-related issues.
These vulnerabilities may enable data exposure, injection attacks, authentication or authorization bypasses, and weak cryptographic implementations.

Due to their nature, all Vulnerabilities are considered high priority, regardless of their nominal severity classification.

### 3.2 Reliability: Bugs

A total of 312 Bugs were identified, many of which are classified as CRITICAL or MAJOR.
These issues affect functional correctness, runtime stability, error handling, and edge-case behavior.

From a dependability perspective, Bugs directly undermine system reliability and must be addressed before any structural refactoring or optimization activity.

## 4. Criticality Analysis by Quality Dimension

A severity-only interpretation is insufficient to guide effective remediation.
BLOCKER issues represent conditions that may cause system failure, infinite execution paths, or invalid states, preventing the system from being considered production-ready.

CRITICAL issues form the core technical risk of the project, affecting security and reliability in ways that may compromise data integrity or availability.
MAJOR issues increase long-term technical risk, while MINOR issues mainly affect readability and maintainability and are intentionally deprioritized in the initial remediation phase.

## 5. Risk-Oriented Interpretation

To align technical findings with engineering decision-making, issues were reclassified according to their dominant quality impact.

///GRAFICO


Despite the numerical prevalence of maintainability-related issues, the analysis clearly shows that security and reliability constitute the highest operational risk and therefore drive remediation priorities.

## 6. Initial Remediation Strategy and Priority Plan

Based on the analysis, a phased remediation strategy was defined following a strict **risk-first approach**.

### Phase 1 – Security Hardening
- Fix all detected Vulnerabilities  
- Resolve BLOCKER and CRITICAL issues related to security  
- Enforce secure coding practices  

### Phase 2 – Reliability Stabilization
- Address CRITICAL and MAJOR Bugs  
- Improve error handling and defensive logic  
- Reduce runtime failure risks  

### Phase 3 – Structural Quality Improvements
- Refactor selected MAJOR Code Smells  
- Improve extensibility and architectural clarity  

### Phase 4 – Maintainability Cleanup
- Resolve remaining MINOR Code Smells  
- Apply cosmetic and stylistic improvements  

> **TODO:** Insert remediation priority timeline or flow diagram.

This phased approach ensures that **security and dependability are treated as first-class concerns**, while maintainability improvements are addressed only after achieving a stable and secure baseline.

---

7. Traceability: Issue-Based Analysis (SonarCloud Rules)

To guarantee full traceability and auditability, the most frequently detected violations are reported below, classified by SonarCloud rule ID, including issue type, severity, occurrence count, and representative locations.

| Rule ID                       | Type          | Severity | Count | Main Locations (Examples)                                 |
| ----------------------------- | ------------- | -------- | ----- | --------------------------------------------------------- |
| Web:S7930                     | BUG           | CRITICAL | 226   | Account.jsp, chat.jsp, Conversazioni.jsp                  |
| java:S125                     | CODE_SMELL    | MAJOR    | 131   | Resto.java, Studente.java, Topic.java                     |
| java:S1128                    | CODE_SMELL    | MINOR    | 99    | Resto.java, Studente.java, IndexServlet.java              |
| Web:ItemTagNotWithinContainer | BUG           | MINOR    | 61    | Account.jsp, Conversazioni.jsp, aula.jsp                  |
| java:S1989                    | VULNERABILITY | MINOR    | 42    | EdificioServlet.java, IndexServlet.java, ChatServlet.java |
| Web:S6844                     | CODE_SMELL    | MAJOR    | 40    | Account.jsp, chat.jsp, Conversazioni.jsp                  |
| javascript:S3504              | CODE_SMELL    | CRITICAL | 23    | formOrario.js, formChat.js, trovaNonAttivati.js           |
| java:S106                     | CODE_SMELL    | MAJOR    | 22    | IndexServlet.java, inviaMessaggioChatServlet.java         |
| java:S2190                    | BUG           | BLOCKER  | 17    | cercaOrario.java (infinite recursion)                     |
| Web:S5254                     | BUG           | MAJOR    | 15    | Conversazioni.jsp, ErroreAccesso.jsp, Login.jsp           |

This assessment establishes a clear and measurable baseline for the project’s quality and security posture.
The analysis reveals a significant concentration of high-severity issues, with security and reliability risks outweighing maintainability concerns.

The defined remediation strategy provides a structured and risk-aware path forward, ensuring that future development activities are built upon a secure, reliable, and controlled foundation.
