package it.unisa.uniclass.testing.benchmark.jmh.utenti.JMH;

import it.unisa.uniclass.common.exceptions.AuthenticationException;
import it.unisa.uniclass.common.exceptions.NotFoundUserException;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo;
import it.unisa.uniclass.utenti.model.Tipo;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UtenteService;
import it.unisa.uniclass.utenti.service.dao.AccademicoRemote;
import it.unisa.uniclass.utenti.service.dao.UtenteRemote;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;
import org.openjdk.jmh.results.format.ResultFormatType;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.TimeUnit;

import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.doNothing;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

@State(Scope.Thread)
@BenchmarkMode({Mode.Throughput, Mode.AverageTime, Mode.SampleTime, Mode.SingleShotTime})
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@Warmup(iterations = 10, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 10, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(3)
public class UtenteServiceBenchmark {

    private UtenteService utenteService;
    private Utente utenteStatico;
    private Accademico accademicoStatico;

    private static final String EMAIL_UTENTE = "utente@unisa.it";
    private static final String PASS_UTENTE = "password123";
    private static final String EMAIL_ACCADEMICO = "prof@unisa.it";
    private static final String PASS_ACCADEMICO = "passProf";
    private static final String EMAIL_INESISTENTE = "inesistente@unisa.it";

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
        utenteStatico = new Utente();
        utenteStatico.setEmail(EMAIL_UTENTE);
        utenteStatico.setPassword(PASS_UTENTE);
        utenteStatico.setTipo(Tipo.PersonaleTA);
        utenteStatico.setNome("Mario");
        utenteStatico.setCognome("Rossi");

        accademicoStatico = new Accademico();
        accademicoStatico.setEmail(EMAIL_ACCADEMICO);
        accademicoStatico.setPassword(PASS_ACCADEMICO);
        accademicoStatico.setRuolo(Ruolo.DOCENTE);
        accademicoStatico.setMatricola("D001234");
        accademicoStatico.setNome("Luigi");
        accademicoStatico.setCognome("Verdi");

        UtenteRemote mockUtenteDAO = mock(UtenteRemote.class);
        AccademicoRemote mockAccademicoDAO = mock(AccademicoRemote.class);

        when(mockUtenteDAO.login(EMAIL_UTENTE, PASS_UTENTE)).thenReturn(utenteStatico);
        when(mockUtenteDAO.login(EMAIL_ACCADEMICO, PASS_ACCADEMICO)).thenReturn(accademicoStatico);
        when(mockUtenteDAO.login(EMAIL_INESISTENTE, "wrong")).thenReturn(null);
        when(mockUtenteDAO.findByEmail(EMAIL_UTENTE)).thenReturn(utenteStatico);
        when(mockUtenteDAO.findByEmail(EMAIL_ACCADEMICO)).thenReturn(accademicoStatico);
        when(mockUtenteDAO.findByEmail(EMAIL_INESISTENTE)).thenReturn(null);
        when(mockUtenteDAO.findAll()).thenReturn(Arrays.asList(utenteStatico, accademicoStatico));
        doNothing().when(mockUtenteDAO).update(any(Utente.class));

        List<Accademico> listaDocenti = Collections.singletonList(accademicoStatico);
        when(mockAccademicoDAO.findByRole(Ruolo.DOCENTE)).thenReturn(listaDocenti);
        when(mockAccademicoDAO.findByRole(Ruolo.STUDENTE)).thenReturn(Collections.emptyList());
        doNothing().when(mockAccademicoDAO).update(any(Accademico.class));

        utenteService = new UtenteService(mockUtenteDAO, mockAccademicoDAO);
    }

    @Benchmark
    public void benchmarkLogin(Blackhole bh) {
        try {
            bh.consume(utenteService.login(EMAIL_UTENTE, PASS_UTENTE));
        } catch (AuthenticationException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkLoginAccademico(Blackhole bh) {
        try {
            bh.consume(utenteService.login(EMAIL_ACCADEMICO, PASS_ACCADEMICO));
        } catch (AuthenticationException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetUtenteByEmail(Blackhole bh) {
        try {
            bh.consume(utenteService.getUtenteByEmail(EMAIL_UTENTE));
        } catch (NotFoundUserException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetAccademiciPerRuolo(Blackhole bh) {
        bh.consume(utenteService.getAccademiciPerRuolo(Ruolo.DOCENTE));
    }

    @Benchmark
    public void benchmarkGetTuttiGliUtenti(Blackhole bh) {
        bh.consume(utenteService.getTuttiGliUtenti());
    }

    @Benchmark
    public void benchmarkLoginFallito(Blackhole bh) {
        try {
            bh.consume(utenteService.login(EMAIL_INESISTENTE, "wrong"));
        } catch (AuthenticationException e) {
            bh.consume(e);
        }
    }
}
