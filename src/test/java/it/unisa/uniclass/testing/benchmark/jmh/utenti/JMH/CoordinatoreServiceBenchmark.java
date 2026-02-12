package it.unisa.uniclass.testing.benchmark.jmh.utenti.JMH;

import it.unisa.uniclass.testing.benchmark.jmh.utenti.mocks.MockCoordinatoreDAO;
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
public class CoordinatoreServiceBenchmark {

    private CoordinatoreService coordService;

    private static final String EMAIL = "coord@unisa.it";
    private static final String CORSO = "Informatica";

    public static void main(String[] args) throws RunnerException {
        Options opt = new OptionsBuilder()
                .include(CoordinatoreServiceBenchmark.class.getSimpleName())
                .forks(3)
                .warmupIterations(10)
                .measurementIterations(10)
                .mode(Mode.All)
                .warmupTime(org.openjdk.jmh.runner.options.TimeValue.seconds(1))
                .measurementTime(org.openjdk.jmh.runner.options.TimeValue.seconds(1))
                .timeUnit(TimeUnit.MICROSECONDS)
                .resultFormat(ResultFormatType.JSON)
                .result("jmh-result-coordinatore.json")
                .jvmArgs("-Djmh.ignoreLock=true")
                .build();

        new Runner(opt).run();
    }

    @Setup(Level.Trial)
    public void setup() {
        MockCoordinatoreDAO mockDao = new MockCoordinatoreDAO();
        Coordinatore c = new Coordinatore();
        c.setEmail(EMAIL);
        c.setMatricola("001122");

        mockDao.setCoordinatoreDaRitornare(c);
        this.coordService = new CoordinatoreService(mockDao);
    }

    @Benchmark
    public void benchmarkTrovaPerEmail(Blackhole bh) {
        bh.consume(coordService.trovaCoordinatoreEmailUniclass(EMAIL));
    }

    @Benchmark
    public void benchmarkTrovaTutti(Blackhole bh) {
        bh.consume(coordService.trovaTutti());
    }

    @Benchmark
    public void benchmarkTrovaPerEmailFallito(Blackhole bh) {
        bh.consume(coordService.trovaCoordinatoreEmailUniclass("inesistente@unisa.it"));
    }
}
