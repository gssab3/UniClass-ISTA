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

import java.util.Collections;
import java.util.List;
import java.util.concurrent.TimeUnit;

import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

@State(Scope.Thread)
@BenchmarkMode({Mode.Throughput, Mode.AverageTime, Mode.SampleTime, Mode.SingleShotTime})
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@Warmup(iterations = 10, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 10, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(3)
public class DocenteServiceBenchmark {

    private UserDirectoryImpl userDirectory;
    private Accademico docenteStatico;

    private static final String EMAIL_DOCENTE = "docente@unisa.it";
    private static final String EMAIL_INESISTENTE = "inesistente@unisa.it";

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
        docenteStatico = new Accademico();
        docenteStatico.setRuolo(Ruolo.DOCENTE);
        docenteStatico.setEmail(EMAIL_DOCENTE);
        docenteStatico.setMatricola("D005566");
        docenteStatico.setNome("Luca");
        docenteStatico.setCognome("Verdi");

        UtenteService mockUtenteService = mock(UtenteService.class);

        try {
            when(mockUtenteService.getUtenteByEmail(EMAIL_DOCENTE)).thenReturn(docenteStatico);
            when(mockUtenteService.getUtenteByEmail(EMAIL_INESISTENTE)).thenReturn(null);
        } catch (Exception e) {

        }

        List<Accademico> listaDocenti = Collections.singletonList(docenteStatico);
        when(mockUtenteService.getAccademiciPerRuolo(Ruolo.DOCENTE)).thenReturn(listaDocenti);

        when(mockUtenteService.getTuttiGliUtenti()).thenReturn(Collections.singletonList(docenteStatico));

        userDirectory = new UserDirectoryImpl(mockUtenteService);
    }

    @Benchmark
    public void benchmarkIsDocente(Blackhole bh) {
        bh.consume(userDirectory.isDocente(EMAIL_DOCENTE));
    }

    @Benchmark
    public void benchmarkGetAccademico(Blackhole bh) {
        bh.consume(userDirectory.getAccademico(EMAIL_DOCENTE));
    }

    @Benchmark
    public void benchmarkGetAccademiciPerRuoloDocente(Blackhole bh) {
        bh.consume(userDirectory.getAccademiciPerRuolo(Ruolo.DOCENTE));
    }

    @Benchmark
    public void benchmarkIsDocenteFallito(Blackhole bh) {
        bh.consume(userDirectory.isDocente(EMAIL_INESISTENTE));
    }

    @Benchmark
    public void benchmarkGetTuttiGliUtenti(Blackhole bh) {
        bh.consume(userDirectory.getTuttiGliUtenti());
    }
}
