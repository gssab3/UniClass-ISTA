package it.unisa.uniclass.testing.benchmark.utenti.JMH;

import it.unisa.uniclass.testing.benchmark.utenti.mocks.MockPersonaleTADAO;
import it.unisa.uniclass.utenti.model.PersonaleTA;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.util.concurrent.TimeUnit;

@State(Scope.Thread)
@BenchmarkMode({Mode.Throughput, Mode.AverageTime, Mode.SampleTime, Mode.SingleShotTime})
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@Warmup(iterations = 10, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 10, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(3)
public class PersonaleTAServiceBenchmark {

    private PersonaleTAService taService;

    private static final String EMAIL = "admin@unisa.it";
    private static final String PASSWORD = "passwordAdmin";

    @Setup(Level.Trial)
    public void setup() {
        MockPersonaleTADAO mockDao = new MockPersonaleTADAO();

        PersonaleTA personale = new PersonaleTA();
        personale.setEmail(EMAIL);
        personale.setPassword(PASSWORD);

        mockDao.setPersonaleDaRitornare(personale);

        this.taService = new PersonaleTAService(mockDao);
    }

    @Benchmark
    public void benchmarkTrovaEmailPass(Blackhole bh) {
        bh.consume(taService.trovaEmailPass(EMAIL, PASSWORD));
    }

    @Benchmark
    public void benchmarkTrovaEmailErrata(Blackhole bh) {
        bh.consume(taService.trovaEmailPass("inesistente@unisa.it", "passwordSbagliata"));
    }
}
