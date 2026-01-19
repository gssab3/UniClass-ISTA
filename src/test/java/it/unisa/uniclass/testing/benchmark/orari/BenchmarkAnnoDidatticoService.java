package it.unisa.uniclass.testing.benchmark.orari;

import it.unisa.uniclass.orari.model.AnnoDidattico;
import it.unisa.uniclass.orari.service.AnnoDidatticoService;
import it.unisa.uniclass.orari.service.dao.AnnoDidatticoRemote;
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
public class BenchmarkAnnoDidatticoService {

    private AnnoDidatticoService service;
    private AnnoDidattico annoStatico;

    public static void main(String[] args) throws RunnerException {
        Options opt = new OptionsBuilder()
                .include(BenchmarkAnnoDidatticoService.class.getSimpleName())
                .resultFormat(ResultFormatType.JSON)
                .result("jmh-result-anno-didattico.json")
                .build();

        new Runner(opt).run();
    }

    @Setup(Level.Trial)
    public void setUp() {
        AnnoDidatticoRemote mockDao = mock(AnnoDidatticoRemote.class);

        annoStatico = new AnnoDidattico();
        annoStatico.setAnno("Anno 1");

        when(mockDao.trovaAnno(anyString())).thenReturn(Collections.singletonList(annoStatico));
        when(mockDao.trovaId(anyInt())).thenReturn(annoStatico);
        when(mockDao.trovaTutti()).thenReturn(Collections.singletonList(annoStatico));
        when(mockDao.trovaTuttiCorsoLaurea(anyLong())).thenReturn(Collections.singletonList(annoStatico));
        when(mockDao.trovaCorsoLaureaNome(anyLong(), anyString())).thenReturn(annoStatico);

        service = new AnnoDidatticoService(mockDao);
    }

    @Benchmark
    public void trovaAnnoBenchmark(Blackhole bh) {
        bh.consume(service.trovaAnno("Anno 1"));
    }

    @Benchmark
    public void trovaIdBenchmark(Blackhole bh) {
        bh.consume(service.trovaId(1));
    }

    @Benchmark
    public void trovaTuttiBenchmark(Blackhole bh) {
        bh.consume(service.trovaTutti());
    }

    @Benchmark
    public void trovaTuttiCorsoLaureaBenchmark(Blackhole bh) {
        bh.consume(service.trovaTuttiCorsoLaurea(1L));
    }

    @Benchmark
    public void trovaTuttiCorsoLaureaNomeBenchmark(Blackhole bh) {
        bh.consume(service.trovaTuttiCorsoLaureaNome(1L, "Anno 1"));
    }

    @Benchmark
    public void aggiungiAnnoBenchmark(Blackhole bh) {
        service.aggiungiAnno(annoStatico);
        bh.consume(annoStatico);
    }

    @Benchmark
    public void rimuoviAnnoBenchmark(Blackhole bh) {
        service.rimuoviAnno(annoStatico);
        bh.consume(annoStatico);
    }
}

