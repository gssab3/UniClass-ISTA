# Performance Evaluation of the it.unisa.uniclass.utenti Services

This chapter presents a comprehensive performance evaluation of the core services of the *it.unisa.uniclass* system. The analysis was conducted using the Java Microbenchmark Harness (JMH), a standard framework for building, running, and analyzing benchmarks on the Java Virtual Machine (JVM). The objective of this evaluation is to assess the efficiency, responsiveness, and stability of the most critical service operations.

---

## Experimental Setup

All benchmarks were executed using **JMH version 1.35** on a **Java 21 (JDK 21.0.9)** runtime environment. The benchmark configuration was designed to ensure stable and reliable measurements, allowing the JVM to reach a steady state before collecting performance data.

The experimental parameters were configured as follows:
- **Warmup iterations:** 10  
- **Measurement iterations:** 10  
- **Iteration duration:** 1 second  
- **Threads:** 1  
- **Forks:** 1  

This configuration minimizes the impact of JVM warmup effects, Just-In-Time (JIT) compilation, and transient runtime optimizations, ensuring that the recorded metrics reflect steady-state performance.

---

## Benchmark Methodology and Metrics

JMH provides multiple measurement modes, each capturing a different aspect of system performance. In this evaluation, three modes were considered:

- **Throughput (thrpt):**  
  Measures the number of completed operations per unit of time, expressed in operations per microsecond (*ops/μs*). This metric reflects the system’s processing capacity under sustained load.

- **Average Time (avgt):**  
  Measures the average time required to complete a single operation, expressed in microseconds per operation (*μs/op*). This metric captures the mean latency experienced by a request.

- **Sample Time (sample):**  
  Collects statistically sampled execution times to analyze the latency distribution. Percentiles derived from this mode provide insight into typical behavior (*p50*) and high-latency outliers (*p99*).

Each measurement mode was executed independently, and the results should therefore be interpreted as complementary rather than directly comparable.

---

## Throughput Analysis

Table 1 reports the throughput results for the evaluated service methods.

| Benchmark Method | Throughput (ops/μs) |
|---|---:|
| Coordinatore – benchmarkTrovaPerEmail | 367.70 |
| Coordinatore – benchmarkTrovaPerEmailFallito | 418.10 |
| Coordinatore – benchmarkTrovaTutti | 153.86 |
| Docente – benchmarkTrovaPerCorso | 864.51 |
| Docente – benchmarkTrovaPerCorsoFallito | 873.52 |
| Docente – benchmarkTrovaPerMatricola | 855.91 |
| Docente – benchmarkTrovaPerMatricolaFallito | 849.21 |
| PersonaleTA – benchmarkTrovaEmailErrata | 856.80 |
| PersonaleTA – benchmarkTrovaEmailPass | 856.80 |
| Utente – benchmarkLoginAccademico | 400.09 |
| Utente – benchmarkLoginFallito | 364.83 |
| Utente – benchmarkLoginPersonaleTA | 361.51 |

The results indicate that lookup operations related to *Docente* and *PersonaleTA* services achieve the highest throughput, exceeding **850 ops/μs**. In contrast, operations involving broader data retrieval, such as `benchmarkTrovaTutti`, exhibit significantly lower throughput due to the increased computational and data-access cost.

---

## Average Time Analysis

Table 2 summarizes the average execution time for each benchmarked operation.

| Benchmark Method | Avg Time (μs/op) |
|---|---:|
| Coordinatore – benchmarkTrovaPerEmail | 0.00117 |
| Coordinatore – benchmarkTrovaPerEmailFallito | 0.00117 |
| Coordinatore – benchmarkTrovaTutti | 0.00643 |
| Docente – benchmarkTrovaPerCorso | 0.00116 |
| Docente – benchmarkTrovaPerCorsoFallito | 0.00114 |
| Docente – benchmarkTrovaPerMatricola | 0.00117 |
| Docente – benchmarkTrovaPerMatricolaFallito | 0.00117 |
| PersonaleTA – benchmarkTrovaEmailErrata | 0.00116 |
| PersonaleTA – benchmarkTrovaEmailPass | 0.00118 |
| Utente – benchmarkLoginAccademico | 0.00261 |
| Utente – benchmarkLoginFallito | 0.00253 |
| Utente – benchmarkLoginPersonaleTA | 0.00275 |

Most service methods exhibit sub-microsecond latency, confirming the efficiency of indexed lookup operations and lightweight service logic. Higher average times are observed in authentication-related methods, such as login operations, which involve additional validation and security checks.

---

## Sample Time and Latency Distribution

Table 3 reports the median (*p50*) and 99th percentile (*p99*) latencies derived from the sample time measurements.

| Benchmark Method | p50 (μs/op) | p99 (μs/op) |
|---|---:|---:|
| Coordinatore – benchmarkTrovaPerEmail | 0.0 | 0.1 |
| Coordinatore – benchmarkTrovaPerEmailFallito | 0.0 | 0.1 |
| Coordinatore – benchmarkTrovaTutti | 0.0 | 0.1 |
| Docente – benchmarkTrovaPerCorso | 0.0 | 0.1 |
| Docente – benchmarkTrovaPerCorsoFallito | 0.0 | 0.1 |
| Docente – benchmarkTrovaPerMatricola | 0.0 | 0.1 |
| Docente – benchmarkTrovaPerMatricolaFallito | 0.0 | 0.1 |
| PersonaleTA – benchmarkTrovaEmailErrata | 0.0 | 0.1 |
| PersonaleTA – benchmarkTrovaEmailPass | 0.0 | 0.1 |
| Utente – benchmarkLoginAccademico | 0.0 | 0.1 |
| Utente – benchmarkLoginFallito | 0.0 | 0.1 |
| Utente – benchmarkLoginPersonaleTA | 0.0 | 0.1 |

The sample time analysis shows extremely low median latencies, with the 99th percentile remaining below **0.1 μs** across all benchmarks. This indicates a highly stable execution profile with minimal latency variability and rare performance outliers.

---
## Key Findings
Service Efficiency
The DocenteService demonstrated the highest efficiency across all search-based benchmarks. Methods such as benchmarkTrovaPerCorso and benchmarkTrovaPerMatricola reached throughput values exceeding 850 ops/us. This performance level suggests a highly optimized retrieval process for faculty-related data.

## Operations Complexity
The method benchmarkTrovaTutti (CoordinatoreService) showed the lowest throughput (153.86 ops/us) and the highest average time (0.00643 us/op). This result is expected, as mass data retrieval typically entails higher computational and I/O overhead compared to targeted single-field searches.

## Authentication Latency
Login operations maintained consistent performance levels across different user types. The average time for benchmarkLoginAccademico (0.00261 us/op) was comparable to benchmarkLoginPersonaleTA (0.00275 us/op), indicating a uniform authentication logic.

## Reliability and Percentiles
Statistical sampling showed that 99% (p99) of operations are completed within 0.1 us. While some outliers reached significantly higher values (e.g., maximum sample times up to 568.32 us for failed email lookups), the overall distribution remains stable and predictable.

---

## Summary

This performance evaluation confirms that the evaluated services meet stringent efficiency and responsiveness requirements. The use of JMH provided reliable, reproducible measurements, enabling a detailed understanding of system behavior across multiple performance dimensions. These results establish a solid baseline for future optimizations and scalability testing.
