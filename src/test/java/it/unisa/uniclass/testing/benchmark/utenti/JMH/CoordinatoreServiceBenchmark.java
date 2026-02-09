package it.unisa.uniclass.testing.benchmark.utenti.JMH;

import it.unisa.uniclass.testing.benchmark.utenti.mocks.MockCoordinatoreDAO;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

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
