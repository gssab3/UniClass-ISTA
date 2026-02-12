package it.unisa.uniclass.testing.benchmark.jmh.utenti;

import it.unisa.uniclass.common.exceptions.AuthenticationException;
import it.unisa.uniclass.utenti.model.Tipo;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UtenteService;
import it.unisa.uniclass.utenti.service.UserDirectoryImpl;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;
import org.openjdk.jmh.results.format.ResultFormatType;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;

import java.util.Collections;
import java.util.concurrent.TimeUnit;

import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

@State(Scope.Thread)
@BenchmarkMode({Mode.Throughput, Mode.AverageTime, Mode.SampleTime, Mode.SingleShotTime})
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@Warmup(iterations = 10, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 10, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(3)
public class PersonaleTAServiceBenchmark {

    private UserDirectoryImpl userDirectory;
    private Utente personaleTAStatico;

    private static final String EMAIL_PTA = "admin@unisa.it";
    private static final String PASSWORD = "passwordAdmin";
    private static final String EMAIL_INESISTENTE = "inesistente@unisa.it";

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
        personaleTAStatico = new Utente();
        personaleTAStatico.setTipo(Tipo.PersonaleTA);
        personaleTAStatico.setEmail(EMAIL_PTA);
        personaleTAStatico.setPassword(PASSWORD);
        personaleTAStatico.setNome("Admin");
        personaleTAStatico.setCognome("Sistema");

        UtenteService mockUtenteService = mock(UtenteService.class);

        try {
            when(mockUtenteService.getUtenteByEmail(EMAIL_PTA)).thenReturn(personaleTAStatico);
            when(mockUtenteService.getUtenteByEmail(EMAIL_INESISTENTE)).thenReturn(null);
            when(mockUtenteService.login(EMAIL_PTA, PASSWORD)).thenReturn(personaleTAStatico);
            when(mockUtenteService.login(EMAIL_INESISTENTE, "wrong")).thenThrow(new AuthenticationException("Credenziali errate"));
        } catch (Exception e) {

        }

        // getTuttiGliUtenti
        when(mockUtenteService.getTuttiGliUtenti()).thenReturn(Collections.singletonList(personaleTAStatico));

        // 4. Inietta il mock nel service tramite costruttore
        userDirectory = new UserDirectoryImpl(mockUtenteService);
    }

    @Benchmark
    public void benchmarkLogin(Blackhole bh) {
        try {
            bh.consume(userDirectory.login(EMAIL_PTA, PASSWORD));
        } catch (Exception e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetUser(Blackhole bh) {
        bh.consume(userDirectory.getUser(EMAIL_PTA));
    }

    @Benchmark
    public void benchmarkGetTuttiGliUtenti(Blackhole bh) {
        bh.consume(userDirectory.getTuttiGliUtenti());
    }

    @Benchmark
    public void benchmarkLoginFallito(Blackhole bh) {
        try {
            bh.consume(userDirectory.login(EMAIL_INESISTENTE, "wrong"));
        } catch (Exception e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetUserInesistente(Blackhole bh) {
        bh.consume(userDirectory.getUser(EMAIL_INESISTENTE));
    }
}
