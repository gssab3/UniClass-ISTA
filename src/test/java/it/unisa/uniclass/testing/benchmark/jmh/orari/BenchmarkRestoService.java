package it.unisa.uniclass.testing.benchmark.jmh.orari;

import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.model.Resto;
import it.unisa.uniclass.orari.service.RestoService;
import it.unisa.uniclass.orari.service.dao.RestoRemote;
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
public class BenchmarkRestoService {

    private RestoService service;
    private Resto restoStatico;
    private CorsoLaurea corsoLaurea;

    public static void main(String[] args) throws RunnerException {
        Options opt = new OptionsBuilder()
                .include(BenchmarkRestoService.class.getSimpleName())
                .resultFormat(ResultFormatType.JSON)
                .result("jmh-result-resto.json")
                .build();

        new Runner(opt).run();
    }

    @Setup(Level.Trial)
    public void setUp() {
        RestoRemote mockDao = mock(RestoRemote.class);

        corsoLaurea = new CorsoLaurea();
        corsoLaurea.setNome("Informatica");

        restoStatico = new Resto();
        restoStatico.setNome("Resto 0");
        restoStatico.setCorsoLaurea(corsoLaurea);

        when(mockDao.trovaRestiCorsoLaurea(any(CorsoLaurea.class))).thenReturn(Collections.singletonList(restoStatico));
        when(mockDao.trovaRestiCorsoLaurea(anyString())).thenReturn(Collections.singletonList(restoStatico));
        when(mockDao.trovaResto(anyString())).thenReturn(Collections.singletonList(restoStatico));
        when(mockDao.trovaResto(anyLong())).thenReturn(restoStatico);
        when(mockDao.trovaRestoNomeCorso(anyString(), any(CorsoLaurea.class))).thenReturn(restoStatico);
        when(mockDao.trovaRestoNomeCorso(anyString(), anyString())).thenReturn(restoStatico);

        service = new RestoService(mockDao);
    }

    @Benchmark
    public void trovaRestiCorsoLaureaObjBenchmark(Blackhole bh) {
        bh.consume(service.trovaRestiCorsoLaurea(corsoLaurea));
    }

    @Benchmark
    public void trovaRestiCorsoLaureaNomeBenchmark(Blackhole bh) {
        bh.consume(service.trovaRestiCorsoLaurea("Informatica"));
    }

    @Benchmark
    public void trovaRestoNomeBenchmark(Blackhole bh) {
        bh.consume(service.trovaResto("Resto 0"));
    }

    @Benchmark
    public void trovaRestoIdBenchmark(Blackhole bh) {
        bh.consume(service.trovaResto(1L));
    }

    @Benchmark
    public void trovaRestoNomeCorsoObjBenchmark(Blackhole bh) {
        bh.consume(service.trovaRestoNomeCorso("Resto 0", corsoLaurea));
    }

    @Benchmark
    public void trovaRestoNomeCorsoStringBenchmark(Blackhole bh) {
        bh.consume(service.trovaRestoNomeCorso("Resto 0", "Informatica"));
    }

    @Benchmark
    public void aggiungiRestoBenchmark(Blackhole bh) {
        service.aggiungiResto(restoStatico);
        bh.consume(restoStatico);
    }

    @Benchmark
    public void rimuoviRestoBenchmark(Blackhole bh) {
        service.rimuoviResto(restoStatico);
        bh.consume(restoStatico);
    }
}

