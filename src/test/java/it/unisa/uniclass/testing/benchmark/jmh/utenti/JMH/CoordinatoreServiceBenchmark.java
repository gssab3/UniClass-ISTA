package it.unisa.uniclass.testing.benchmark.jmh.utenti.JMH;

import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo;
import it.unisa.uniclass.utenti.service.UtenteService;
import it.unisa.uniclass.utenti.service.UserDirectoryImpl;
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

import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

@State(Scope.Thread)
@BenchmarkMode({Mode.Throughput, Mode.AverageTime, Mode.SampleTime, Mode.SingleShotTime})
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@Warmup(iterations = 10, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 10, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(3)
public class CoordinatoreServiceBenchmark {

    private UserDirectoryImpl userDirectory;
    private Accademico coordinatoreStatico;

    private static final String EMAIL_COORDINATORE = "coord@unisa.it";
    private static final String EMAIL_INESISTENTE = "inesistente@unisa.it";

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
        coordinatoreStatico = new Accademico();
        coordinatoreStatico.setRuolo(Ruolo.COORDINATORE);
        coordinatoreStatico.setEmail(EMAIL_COORDINATORE);
        coordinatoreStatico.setMatricola("C001122");
        coordinatoreStatico.setNome("Mario");
        coordinatoreStatico.setCognome("Rossi");

        // 2. Crea il mock di UtenteService (dipendenza di UserDirectoryImpl)
        UtenteService mockUtenteService = mock(UtenteService.class);

        try {
            when(mockUtenteService.getUtenteByEmail(EMAIL_COORDINATORE)).thenReturn(coordinatoreStatico);
            when(mockUtenteService.getUtenteByEmail(EMAIL_INESISTENTE)).thenReturn(null);
        } catch (Exception e) {
            // Gestisce eccezioni checked
        }

        // getAccademiciPerRuolo(COORDINATORE) ritorna lista di coordinatori
        List<Accademico> listaCoordinatori = Arrays.asList(coordinatoreStatico);
        when(mockUtenteService.getAccademiciPerRuolo(Ruolo.COORDINATORE)).thenReturn(listaCoordinatori);

        // getTuttiGliUtenti
        when(mockUtenteService.getTuttiGliUtenti()).thenReturn(Collections.singletonList(coordinatoreStatico));

        // 4. Inietta il mock nel service tramite costruttore
        userDirectory = new UserDirectoryImpl(mockUtenteService);
    }

    @Benchmark
    public void benchmarkIsCoordinatore(Blackhole bh) {
        bh.consume(userDirectory.isCoordinatore(EMAIL_COORDINATORE));
    }

    @Benchmark
    public void benchmarkGetAccademico(Blackhole bh) {
        bh.consume(userDirectory.getAccademico(EMAIL_COORDINATORE));
    }

    @Benchmark
    public void benchmarkGetAccademiciPerRuoloCoordinatore(Blackhole bh) {
        bh.consume(userDirectory.getAccademiciPerRuolo(Ruolo.COORDINATORE));
    }

    @Benchmark
    public void benchmarkIsCoordinatoreFallito(Blackhole bh) {
        bh.consume(userDirectory.isCoordinatore(EMAIL_INESISTENTE));
    }

    @Benchmark
    public void benchmarkGetTuttiGliUtenti(Blackhole bh) {
        bh.consume(userDirectory.getTuttiGliUtenti());
    }
}
