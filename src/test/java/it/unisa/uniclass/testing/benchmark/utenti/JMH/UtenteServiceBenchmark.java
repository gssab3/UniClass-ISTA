package it.unisa.uniclass.testing.benchmark.utenti.JMH;

import it.unisa.uniclass.testing.benchmark.utenti.mocks.MockAccademicoDAO;
import it.unisa.uniclass.testing.benchmark.utenti.mocks.MockPersonaleTADAO;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.PersonaleTA;
import it.unisa.uniclass.utenti.service.UtenteService;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

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
