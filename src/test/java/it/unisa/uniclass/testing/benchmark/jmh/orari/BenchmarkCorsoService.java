package it.unisa.uniclass.testing.benchmark.jmh.orari;

import it.unisa.uniclass.orari.model.Corso;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.service.CorsoService;
import it.unisa.uniclass.orari.service.dao.CorsoRemote;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;
import org.openjdk.jmh.results.format.ResultFormatType;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;

import java.util.Collections;
import java.util.concurrent.TimeUnit;

import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

@BenchmarkMode(Mode.All)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(2)
@State(Scope.Benchmark)
public class BenchmarkCorsoService {

    private CorsoService service;
    private Corso corsoStatico;

    public static void main(String[] args) throws RunnerException {
        Options opt = new OptionsBuilder()
                .include(BenchmarkCorsoService.class.getSimpleName())
                .resultFormat(ResultFormatType.JSON)
                .result("jmh-result-corso.json")
                .build();

        new Runner(opt).run();
    }

    @Setup(Level.Trial)
    public void setUp() {
        CorsoRemote mockDao = mock(CorsoRemote.class);

        CorsoLaurea corsoLaurea = new CorsoLaurea();
        corsoLaurea.setNome("Informatica");

        corsoStatico = new Corso();
        corsoStatico.setNome("Programmazione");
        corsoStatico.setCorsoLaurea(corsoLaurea);

        when(mockDao.trovaCorso(anyLong())).thenReturn(corsoStatico);
        when(mockDao.trovaCorsiCorsoLaurea(anyString())).thenReturn(Collections.singletonList(corsoStatico));
        when(mockDao.trovaTutti()).thenReturn(Collections.singletonList(corsoStatico));

        service = new CorsoService(mockDao);
    }

    @Benchmark
    public void trovaCorsoIdBenchmark(Blackhole bh) {
        bh.consume(service.trovaCorso(1L));
    }

    @Benchmark
    public void trovaCorsiCorsoLaureaBenchmark(Blackhole bh) {
        bh.consume(service.trovaCorsiCorsoLaurea("Informatica"));
    }

    @Benchmark
    public void trovaTuttiBenchmark(Blackhole bh) {
        bh.consume(service.trovaTutti());
    }

    @Benchmark
    public void aggiungiCorsoBenchmark(Blackhole bh) {
        service.aggiungiCorso(corsoStatico);
        bh.consume(corsoStatico);
    }

    @Benchmark
    public void rimuoviCorsoBenchmark(Blackhole bh) {
        service.rimuoviCorso(corsoStatico);
        bh.consume(corsoStatico);
    }
}

