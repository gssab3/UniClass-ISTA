package it.unisa.uniclass.testing.benchmark.jmh.utenti.JMH;

import it.unisa.uniclass.testing.benchmark.jmh.utenti.mocks.MockAccademicoDAO;
import it.unisa.uniclass.testing.benchmark.jmh.utenti.mocks.MockPersonaleTADAO;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.PersonaleTA;
import it.unisa.uniclass.utenti.service.UtenteService;
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
public class UtenteServiceBenchmark {

    private UtenteService utenteService;

    private static final String EMAIL_TA = "ta@unisa.it";
    private static final String PASS_TA = "passwordTA";

    private static final String EMAIL_ACC = "prof@unisa.it";
    private static final String PASS_ACC = "passProf";

    private static final String EMAIL_INESISTENTE = "inesistente@unisa.it";
    private static final String PASS_ERRATA = "errata";

    public static void main(String[] args) throws RunnerException {
        Options opt = new OptionsBuilder()
                .include(UtenteServiceBenchmark.class.getSimpleName())
                .forks(3)
                .warmupIterations(10)
                .measurementIterations(10)
                .mode(Mode.All)
                .warmupTime(org.openjdk.jmh.runner.options.TimeValue.seconds(1))
                .measurementTime(org.openjdk.jmh.runner.options.TimeValue.seconds(1))
                .timeUnit(TimeUnit.MICROSECONDS)
                .resultFormat(ResultFormatType.JSON)
                .result("jmh-result-utente.json")
                .jvmArgs("-Djmh.ignoreLock=true")
                .build();

        new Runner(opt).run();
    }

    @Setup(Level.Trial)
    public void setup() {
        utenteService = new UtenteService();

        // Mock PersonaleTA
        MockPersonaleTADAO mockTaDao = new MockPersonaleTADAO();
        PersonaleTA ta = new PersonaleTA();
        ta.setEmail(EMAIL_TA);
        ta.setPassword(PASS_TA);
        mockTaDao.setPersonaleDaRitornare(ta);

        PersonaleTAService taService = new PersonaleTAService(mockTaDao);

        // Mock Accademico
        MockAccademicoDAO mockAccDao = new MockAccademicoDAO();
        Accademico acc = new Accademico();
        acc.setEmail(EMAIL_ACC);
        acc.setPassword(PASS_ACC);
        mockAccDao.setAccademicoDaRitornare(acc);

        AccademicoService accService = new AccademicoService(mockAccDao);

        // Injection
        utenteService.setPersonaleTAService(taService);
        utenteService.setAccademicoService(accService);
    }

    @Benchmark
    public void benchmarkLoginPersonaleTA(Blackhole bh) {
        bh.consume(utenteService.retrieveByUserAndPassword(EMAIL_TA, PASS_TA));
    }

    @Benchmark
    public void benchmarkLoginAccademico(Blackhole bh) {
        bh.consume(utenteService.retrieveByUserAndPassword(EMAIL_ACC, PASS_ACC));
    }

    @Benchmark
    public void benchmarkLoginFallito(Blackhole bh) {
        bh.consume(utenteService.retrieveByUserAndPassword(EMAIL_INESISTENTE, PASS_ERRATA));
    }
}
