package it.unisa.uniclass.testing.benchmark.jmh.utenti.JMH;

import it.unisa.uniclass.testing.benchmark.jmh.utenti.mocks.MockDocenteDAO;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;
import org.openjdk.jmh.results.format.ResultFormatType;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;

import java.util.concurrent.TimeUnit;

@State(Scope.Thread)
@BenchmarkMode({Mode.Throughput, Mode.AverageTime, Mode.SampleTime, Mode.SingleShotTime})
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@Warmup(iterations = 10, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 10, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(3)
public class DocenteServiceBenchmark {

    private DocenteService docenteService;

    private static final String MATRICOLA = "005566";
    private static final String CORSO = "Informatica";

    public static void main(String[] args) throws RunnerException {
        Options opt = new OptionsBuilder()
                .include(DocenteServiceBenchmark.class.getSimpleName())
                .forks(3)
                .warmupIterations(10)
                .measurementIterations(10)
                .mode(Mode.All)
                .warmupTime(org.openjdk.jmh.runner.options.TimeValue.seconds(1))
                .measurementTime(org.openjdk.jmh.runner.options.TimeValue.seconds(1))
                .timeUnit(TimeUnit.MICROSECONDS)
                .resultFormat(ResultFormatType.JSON)
                .result("jmh-result-docente.json")
                .jvmArgs("-Djmh.ignoreLock=true")
                .build();

        new Runner(opt).run();
    }

    @Setup(Level.Trial)
    public void setup() {
        MockDocenteDAO mockDao = new MockDocenteDAO();
        Docente d = new Docente();
        d.setMatricola(MATRICOLA);
        d.setNome("Luca");
        d.setCognome("Verdi");

        mockDao.setDocenteDaRitornare(d);
        this.docenteService = new DocenteService(mockDao);
    }

    @Benchmark
    public void benchmarkTrovaPerMatricola(Blackhole bh) {
        bh.consume(docenteService.trovaDocenteUniClass(MATRICOLA));
    }

    @Benchmark
    public void benchmarkTrovaPerCorso(Blackhole bh) {
        bh.consume(docenteService.trovaDocenteCorsoLaurea(CORSO));
    }

    @Benchmark
    public void benchmarkTrovaPerMatricolaFallito(Blackhole bh) {
        bh.consume(docenteService.trovaDocenteUniClass("000000"));
    }

    @Benchmark
    public void benchmarkTrovaPerCorsoFallito(Blackhole bh) {
        bh.consume(docenteService.trovaDocenteCorsoLaurea("Chimica"));
    }
}
