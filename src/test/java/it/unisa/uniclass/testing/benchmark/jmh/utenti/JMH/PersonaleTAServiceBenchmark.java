package it.unisa.uniclass.testing.benchmark.jmh.utenti.JMH;

import it.unisa.uniclass.testing.benchmark.jmh.utenti.mocks.MockPersonaleTADAO;
import it.unisa.uniclass.utenti.model.PersonaleTA;
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
public class PersonaleTAServiceBenchmark {

    private PersonaleTAService taService;

    private static final String EMAIL = "admin@unisa.it";
    private static final String PASSWORD = "passwordAdmin";

    public static void main(String[] args) throws RunnerException {
        Options opt = new OptionsBuilder()
                .include(PersonaleTAServiceBenchmark.class.getSimpleName())
                .forks(3)
                .warmupIterations(10)
                .measurementIterations(10)
                .mode(Mode.All)
                .warmupTime(org.openjdk.jmh.runner.options.TimeValue.seconds(1))
                .measurementTime(org.openjdk.jmh.runner.options.TimeValue.seconds(1))
                .timeUnit(TimeUnit.MICROSECONDS)
                .resultFormat(ResultFormatType.JSON)
                .result("jmh-result-personale-ta.json")
                .jvmArgs("-Djmh.ignoreLock=true")
                .build();

        new Runner(opt).run();
    }

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
