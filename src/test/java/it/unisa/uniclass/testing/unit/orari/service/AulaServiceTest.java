package it.unisa.uniclass.testing.unit.orari.service;

import it.unisa.uniclass.orari.model.Aula;
import it.unisa.uniclass.orari.service.AulaService;
import it.unisa.uniclass.orari.service.dao.AulaRemote;
import jakarta.persistence.NoResultException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Test d'unità per la classe AulaService.
 * Versione aggiornata per riflettere l'uso di injection EJB
 * senza lookup JNDI nel costruttore.
 */
@DisplayName("Test per la classe AulaService")
public class AulaServiceTest {

    @Mock
    private AulaRemote aulaDao;

    private AulaService aulaService;
    private Aula aula;

    @BeforeEach
    void setUp() {
        MockitoAnnotations.openMocks(this);
        aulaService = new AulaService(aulaDao);
        aula = new Aula(1, "Edificio A", "Aula 101");
    }

    @Nested
    @DisplayName("Test dei costruttori")
    class CostruttoriTest {

        @Test
        @DisplayName("Costruttore con parametro inietta correttamente il DAO")
        void testCostruttoreConParametro() {
            AulaRemote mockDao = mock(AulaRemote.class);
            AulaService service = new AulaService(mockDao);

            assertNotNull(service);
        }

        @Test
        @DisplayName("Costruttore senza parametri crea comunque l'istanza")
        void testCostruttoreVuoto() {
            AulaService service = new AulaService();
            assertNotNull(service);
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaAula(int id)")
    class TrovaAulaByIdTest {

        @Test
        @DisplayName("trovaAula restituisce aula per ID valido")
        void testTrovaAulaByIdSuccesso() {
            int id = 1;

            when(aulaDao.trovaAula(id)).thenReturn(aula);

            Aula result = aulaService.trovaAula(id);

            assertNotNull(result);
            assertEquals("Aula 101", result.getNome());
            verify(aulaDao, times(1)).trovaAula(id);
        }

        @Test
        @DisplayName("trovaAula restituisce null quando aula non trovata")
        void testTrovaAulaByIdNonTrovata() {
            int id = 999;

            when(aulaDao.trovaAula(id)).thenThrow(new NoResultException("Aula non trovata"));

            Aula result = aulaService.trovaAula(id);

            assertNull(result);
            verify(aulaDao, times(1)).trovaAula(id);
        }

        @Test
        @DisplayName("trovaAula con ID diversi")
        void testTrovaAulaByIdDiversi() {
            for (int id = 1; id <= 3; id++) {
                Aula aulaTest = new Aula(id, "Edificio " + id, "Aula " + (100 + id));

                when(aulaDao.trovaAula(id)).thenReturn(aulaTest);

                Aula result = aulaService.trovaAula(id);

                assertNotNull(result);
                assertEquals(id, result.getId());
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaAula(String nome)")
    class TrovaAulaByNomeTest {

        @Test
        @DisplayName("trovaAula restituisce aula per nome valido")
        void testTrovaAulaByNomeSuccesso() {
            String nome = "Aula 101";

            when(aulaDao.trovaAula(nome)).thenReturn(aula);

            Aula result = aulaService.trovaAula(nome);

            assertNotNull(result);
            assertEquals(nome, result.getNome());
            verify(aulaDao, times(1)).trovaAula(nome);
        }

        @Test
        @DisplayName("trovaAula restituisce null per nome inesistente")
        void testTrovaAulaByNomeNonTrovata() {
            String nome = "Aula Inesistente";

            when(aulaDao.trovaAula(nome)).thenThrow(new NoResultException("Aula non trovata"));

            Aula result = aulaService.trovaAula(nome);

            assertNull(result);
            verify(aulaDao, times(1)).trovaAula(nome);
        }

        @Test
        @DisplayName("trovaAula con nomi diversi")
        void testTrovaAulaByNomeDiversi() {
            String[] nomi = {"Aula 101", "Aula 102", "Aula 201"};

            for (String nome : nomi) {
                Aula aulaTest = new Aula(1, "Edificio A", nome);

                when(aulaDao.trovaAula(nome)).thenReturn(aulaTest);

                Aula result = aulaService.trovaAula(nome);

                assertNotNull(result);
                assertEquals(nome, result.getNome());
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaTutte")
    class TrovaTutteTest {

        @Test
        @DisplayName("trovaTutte restituisce lista di tutte le aule")
        void testTrovaTutteSuccesso() {
            List<Aula> aule = new ArrayList<>();
            aule.add(new Aula(1, "Edificio A", "Aula 101"));
            aule.add(new Aula(2, "Edificio B", "Aula 102"));
            aule.add(new Aula(3, "Edificio A", "Aula 103"));

            when(aulaDao.trovaTutte()).thenReturn(aule);

            List<Aula> result = aulaService.trovaTutte();

            assertNotNull(result);
            assertEquals(3, result.size());
            verify(aulaDao, times(1)).trovaTutte();
        }

        @Test
        @DisplayName("trovaTutte restituisce lista vuota")
        void testTrovaTutteVuoto() {
            when(aulaDao.trovaTutte()).thenReturn(new ArrayList<>());

            List<Aula> result = aulaService.trovaTutte();

            assertNotNull(result);
            assertTrue(result.isEmpty());
        }

        @Test
        @DisplayName("trovaTutte con molte aule")
        void testTrovaTutteMolte() {
            List<Aula> aule = new ArrayList<>();
            for (int i = 1; i <= 50; i++) {
                aule.add(new Aula(i, "Edificio", "Aula " + i));
            }

            when(aulaDao.trovaTutte()).thenReturn(aule);

            List<Aula> result = aulaService.trovaTutte();

            assertEquals(50, result.size());
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaAuleEdificio")
    class TrovaAuleEdificioTest {

        @Test
        @DisplayName("trovaAuleEdificio restituisce aule per edificio valido")
        void testTrovaAuleEdificioSuccesso() {
            String edificio = "Edificio A";
            List<Aula> aule = new ArrayList<>();
            aule.add(new Aula(1, edificio, "Aula 101"));
            aule.add(new Aula(2, edificio, "Aula 102"));

            when(aulaDao.trovaAuleEdificio(edificio)).thenReturn(aule);

            List<Aula> result = aulaService.trovaAuleEdificio(edificio);

            assertNotNull(result);
            assertEquals(2, result.size());
            verify(aulaDao, times(1)).trovaAuleEdificio(edificio);
        }

        @Test
        @DisplayName("trovaAuleEdificio restituisce lista vuota")
        void testTrovaAuleEdificioVuoto() {
            String edificio = "Edificio Inesistente";

            when(aulaDao.trovaAuleEdificio(edificio)).thenReturn(new ArrayList<>());

            List<Aula> result = aulaService.trovaAuleEdificio(edificio);

            assertNotNull(result);
            assertTrue(result.isEmpty());
        }

        @Test
        @DisplayName("trovaAuleEdificio con edifici diversi")
        void testTrovaAuleEdificioDiversi() {
            String[] edifici = {"Edificio A", "Edificio B", "Edificio C"};

            for (String edificio : edifici) {
                List<Aula> aule = new ArrayList<>();
                aule.add(new Aula(1, edificio, "Aula 101"));
                aule.add(new Aula(2, edificio, "Aula 102"));

                when(aulaDao.trovaAuleEdificio(edificio)).thenReturn(aule);

                List<Aula> result = aulaService.trovaAuleEdificio(edificio);

                assertEquals(2, result.size());
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaEdifici")
    class TrovaEdificiTest {

        @Test
        @DisplayName("trovaEdifici restituisce lista di edifici")
        void testTrovaEdificiSuccesso() {
            List<String> edifici = new ArrayList<>();
            edifici.add("Edificio A");
            edifici.add("Edificio B");
            edifici.add("Edificio C");

            when(aulaDao.trovaEdifici()).thenReturn(edifici);

            List<String> result = aulaService.trovaEdifici();

            assertNotNull(result);
            assertEquals(3, result.size());
            verify(aulaDao, times(1)).trovaEdifici();
        }

        @Test
        @DisplayName("trovaEdifici restituisce lista vuota")
        void testTrovaEdificiVuoto() {
            when(aulaDao.trovaEdifici()).thenReturn(new ArrayList<>());

            List<String> result = aulaService.trovaEdifici();

            assertNotNull(result);
            assertTrue(result.isEmpty());
        }

        @Test
        @DisplayName("trovaEdifici con molti edifici")
        void testTrovaEdificiMolti() {
            List<String> edifici = new ArrayList<>();
            for (int i = 1; i <= 20; i++) {
                edifici.add("Edificio " + i);
            }

            when(aulaDao.trovaEdifici()).thenReturn(edifici);

            List<String> result = aulaService.trovaEdifici();

            assertEquals(20, result.size());
        }
    }

    @Nested
    @DisplayName("Test del metodo aggiungiAula")
    class AggiungiAulaTest {

        @Test
        @DisplayName("aggiungiAula aggiunge correttamente un'aula")
        void testAggiungiAulaSuccesso() {
            aulaService.aggiungiAula(aula);
            verify(aulaDao, times(1)).aggiungiAula(aula);
        }

        @Test
        @DisplayName("aggiungiAula aggiunge multiple aule")
        void testAggiungiAulaMultiple() {
            for (int i = 1; i <= 5; i++) {
                Aula aulaTest = new Aula(i, "Edificio", "Aula " + i);

                aulaService.aggiungiAula(aulaTest);

                verify(aulaDao, times(1)).aggiungiAula(aulaTest);
            }
        }

        @Test
        @DisplayName("aggiungiAula aggiorna un'aula esistente")
        void testAggiungiAulaAggiorna() {
            Aula aulaAggiornata = new Aula(1, "Edificio B", "Aula 101 Modificata");

            aulaService.aggiungiAula(aulaAggiornata);

            verify(aulaDao, times(1)).aggiungiAula(aulaAggiornata);
        }

        @Test
        @DisplayName("aggiungiAula lancia IllegalArgumentException per aula null")
        void testAggiungiAulaNull() {
            IllegalArgumentException exception = assertThrows(IllegalArgumentException.class, () -> {
                aulaService.aggiungiAula(null);
            });

            assertTrue(exception.getMessage().contains("must not be null"));
        }
    }

    @Nested
    @DisplayName("Test del metodo rimuoviAula")
    class RimuoviAulaTest {

        @Test
        @DisplayName("rimuoviAula rimuove correttamente un'aula")
        void testRimuoviAulaSuccesso() {
            aulaService.rimuoviAula(aula);
            verify(aulaDao, times(1)).rimuoviAula(aula);
        }

        @Test
        @DisplayName("rimuoviAula rimuove multiple aule")
        void testRimuoviAulaMultiple() {
            for (int i = 1; i <= 5; i++) {
                Aula aulaTest = new Aula(i, "Edificio", "Aula " + i);

                aulaService.rimuoviAula(aulaTest);

                verify(aulaDao, times(1)).rimuoviAula(aulaTest);
            }
        }

        @Test
        @DisplayName("rimuoviAula lancia IllegalArgumentException per aula null")
        void testRimuoviAulaNull() {
            IllegalArgumentException exception = assertThrows(IllegalArgumentException.class, () -> {
                aulaService.rimuoviAula(null);
            });

            assertTrue(exception.getMessage().contains("must not be null"));
        }
    }

    @Nested
    @DisplayName("Test di gestione eccezioni")
    class GestioneEccezioniTest {

        @Test
        @DisplayName("trovaAula per ID gestisce eccezioni")
        void testTrovaAulaByIdEccezione() {
            int id = -1;

            when(aulaDao.trovaAula(id)).thenThrow(new NoResultException("Not found"));

            assertThrows(NoResultException.class, () -> aulaDao.trovaAula(id));
        }

        @Test
        @DisplayName("trovaAula per nome gestisce eccezioni")
        void testTrovaAulaByNomeEccezione() {
            String nome = "";

            when(aulaDao.trovaAula(nome)).thenThrow(new NoResultException("Not found"));

            assertThrows(NoResultException.class, () -> aulaDao.trovaAula(nome));
        }

        @Test
        @DisplayName("trovaAuleEdificio gestisce eccezioni")
        void testTrovaAuleEdificioEccezione() {
            String edificio = null;

            when(aulaDao.trovaAuleEdificio(edificio)).thenReturn(new ArrayList<>());

            List<Aula> result = aulaService.trovaAuleEdificio(edificio);

            assertTrue(result.isEmpty());
        }
    }

    @Nested
    @DisplayName("Test di integrazione")
    class ScenariComplessiTest {

        @Test
        @DisplayName("Sequenza completa con operazioni multiple")
        void testSequenzaCompleta() {
            aulaService.aggiungiAula(aula);
            verify(aulaDao, times(1)).aggiungiAula(aula);

            when(aulaDao.trovaAula(1)).thenReturn(aula);
            Aula result = aulaService.trovaAula(1);
            assertNotNull(result);

            aulaService.rimuoviAula(aula);
            verify(aulaDao, atLeastOnce()).rimuoviAula(aula);
        }

        @Test
        @DisplayName("Ricerca per edificio e modifica")
        void testRicercaEdificioEModifica() {
            String edificio = "Edificio A";
            List<Aula> aule = new ArrayList<>();
            Aula aula1 = new Aula(1, edificio, "Aula 101");
            Aula aula2 = new Aula(2, edificio, "Aula 102");
            aule.add(aula1);
            aule.add(aula2);

            when(aulaDao.trovaAuleEdificio(edificio)).thenReturn(aule);

            List<Aula> result = aulaService.trovaAuleEdificio(edificio);
            assertEquals(2, result.size());

            result.getFirst().setNome("Aula 101 Modificata");
            aulaService.aggiungiAula(result.getFirst());

            verify(aulaDao, times(1)).aggiungiAula(result.getFirst());
        }

        @Test
        @DisplayName("Ricerca per nome e aggiornamento")
        void testRicercaNomeEAggiornamento() {
            String nome = "Aula 101";

            when(aulaDao.trovaAula(nome)).thenReturn(aula);

            Aula result = aulaService.trovaAula(nome);
            assertNotNull(result);
            assertEquals(nome, result.getNome());

            result.setEdificio("Edificio B");
            aulaService.aggiungiAula(result);

            verify(aulaDao, times(1)).aggiungiAula(result);
        }
    }
}
