package it.unisa.uniclass.testing.benchmark.jmh.conversazioni;

import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.conversazioni.service.dao.MessaggioRemote;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;
import org.openjdk.jmh.results.format.ResultFormatType;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;
import org.mockito.MockedConstruction;

import javax.naming.InitialContext;
import java.lang.reflect.Field;
import java.util.Collections;
import java.util.concurrent.TimeUnit;

import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.mockConstruction;
import static org.mockito.Mockito.when;

@State(Scope.Benchmark)
public class benchmarkMessaggioService {

    private MessaggioService messaggioService;
    private Messaggio messaggioStatico;

    public static void main(String[] args) throws RunnerException {
        Options opt = new OptionsBuilder()
                .include(benchmarkMessaggioService.class.getSimpleName())

                // --- I TUOI NUOVI PARAMETRI ---
                .forks(3)                   // 3 processi JVM separati (più stabilità)
                .warmupIterations(10)       // 10 iterazioni di riscaldamento
                .measurementIterations(10)  // 10 iterazioni di misura effettiva
                .mode(Mode.All)             // Misura TUTTO: Throughput, AvgTime, SampleTime, ecc.

                // --- CONFIGURAZIONE TEMPO ---
                // Consiglio: riduciamo il tempo per singola iterazione a 1 secondo,
                // altrimenti con Mode.All + 3 Forks il test durerà ORE.
                .warmupTime(org.openjdk.jmh.runner.options.TimeValue.seconds(1))
                .measurementTime(org.openjdk.jmh.runner.options.TimeValue.seconds(1))

                .timeUnit(TimeUnit.MICROSECONDS)
                .resultFormat(ResultFormatType.JSON)
                .result("jmh-result-messaggio.json") // File di output specifico per MessaggioService
                .jvmArgs("-Djmh.ignoreLock=true") // Ignora il lock file JMH
                .build();

        new Runner(opt).run();
    }

    @Setup(Level.Trial)
    public void setUp() throws Exception {
        // 1. Crea il Mock del DAO (lo useremo sia per JNDI che per l'iniezione)
        MessaggioRemote mockDao = mock(MessaggioRemote.class);

        // 2. Prepara un oggetto statico per le risposte (evita allocazioni durante il test)
        messaggioStatico = new Messaggio();
        messaggioStatico.setBody("Benchmark Payload");
        // Se necessario, setta qui altri campi (es. ID, Autore) per evitare NullPointer nel service

        // 3. STUBBING PREVENTIVO
        // Configuriamo Mockito ORA, così durante il benchmark risponde istantaneamente
        when(mockDao.trovaMessaggio(anyLong())).thenReturn(messaggioStatico);
        when(mockDao.trovaTutti()).thenReturn(Collections.singletonList(messaggioStatico));
        when(mockDao.aggiungiMessaggio(any(Messaggio.class))).thenReturn(messaggioStatico);
        // I metodi void non hanno bisogno di stubbing

        // 4. FIX PER IL CRASH "NoInitialContextException"
        // Apriamo un contesto temporaneo dove InitialContext è mockato.
        // Questo serve SOLO per far completare con successo "new MessaggioService()".
        try (MockedConstruction<InitialContext> ctxMock = mockConstruction(InitialContext.class,
                (mock, context) -> {
                    // Quando il costruttore fa lookup, gli diamo il nostro mockDao
                    when(mock.lookup(any(String.class))).thenReturn(mockDao);
                })) {

            // Eseguiamo il costruttore in ambiente "protetto"
            messaggioService = new MessaggioService();
        }
        // Qui il blocco try si chiude e Mockito smette di interferire con le classi di sistema.

        // 5. INIEZIONE VIA REFLECTION
        // Sovrascriviamo il DAO interno per sicurezza, garantendo che usi il nostro mock ottimizzato
        injectDao(messaggioService, mockDao);
    }

    /**
     * Metodo helper per iniettare il mock nel campo privato del service
     */
    private void injectDao(Object targetService, Object daoImplementation) throws Exception {
        Field[] fields = targetService.getClass().getDeclaredFields();
        for (Field field : fields) {
            // Cerca il campo compatibile con l'interfaccia DAO
            if (field.getType().equals(MessaggioRemote.class)) {
                field.setAccessible(true);
                field.set(targetService, daoImplementation);
                return;
            }
        }
        throw new RuntimeException("Impossibile trovare il campo MessaggioRemote nel service!");
    }

    // --- BENCHMARK METHODS ---

    @Benchmark
    public void trovaMessaggioBenchmark(Blackhole bh) {
        bh.consume(messaggioService.trovaMessaggio(1L));
    }

    @Benchmark
    public void trovaTuttiBenchmark(Blackhole bh) {
        bh.consume(messaggioService.trovaTutti());
    }

    @Benchmark
    public void aggiungiMessaggioBenchmark(Blackhole bh) {
        // Usiamo l'oggetto statico per non sporcare la memoria durante il test
        bh.consume(messaggioService.aggiungiMessaggio(messaggioStatico));
    }

    @Benchmark
    public void rimuoviMessaggioBenchmark(Blackhole bh) {
        messaggioService.rimuoviMessaggio(messaggioStatico);
        bh.consume(messaggioStatico);
    }
}