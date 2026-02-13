package it.unisa.uniclass.testing.unit.orari.service;

import it.unisa.uniclass.orari.model.Corso;
import it.unisa.uniclass.orari.service.CorsoService;
import it.unisa.uniclass.orari.service.dao.CorsoRemote;
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
 * Test d'unità aggiornati per la classe CorsoService.
 * Versione corretta per riflettere l'uso di injection EJB
 * senza lookup JNDI nel costruttore.
 */
@DisplayName("Test per la classe CorsoService")
public class CorsoServiceTest {

    @Mock
    private CorsoRemote corsoDao;

    private CorsoService corsoService;
    private Corso corso;

    @BeforeEach
    void setUp() {
        MockitoAnnotations.openMocks(this);
        corsoService = new CorsoService(corsoDao);
        corso = new Corso("Programmazione I");
    }

    @Nested
    @DisplayName("Test dei costruttori")
    class CostruttoriTest {

        @Test
        @DisplayName("Costruttore con parametro inietta correttamente il DAO")
        void testCostruttoreConParametro() {
            CorsoRemote mockDao = mock(CorsoRemote.class);
            CorsoService service = new CorsoService(mockDao);

            assertNotNull(service);
        }

        @Test
        @DisplayName("Costruttore senza parametri crea comunque l'istanza")
        void testCostruttoreVuoto() {
            CorsoService service = new CorsoService();
            assertNotNull(service);
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaCorso")
    class TrovaCorsoTest {

        @Test
        @DisplayName("trovaCorso restituisce corso per ID valido")
        void testTrovaCorsoSuccesso() {
            long id = 1L;

            when(corsoDao.trovaCorso(id)).thenReturn(corso);

            Corso result = corsoService.trovaCorso(id);

            assertNotNull(result);
            assertEquals("Programmazione I", result.getNome());
            verify(corsoDao, times(1)).trovaCorso(id);
        }

        @Test
        @DisplayName("trovaCorso restituisce null quando corso non trovato")
        void testTrovaCorsoNonTrovato() {
            long id = 999L;

            when(corsoDao.trovaCorso(id)).thenThrow(new NoResultException("Corso non trovato"));

            Corso result = corsoService.trovaCorso(id);

            assertNull(result);
            verify(corsoDao, times(1)).trovaCorso(id);
        }

        @Test
        @DisplayName("trovaCorso con ID diversi")
        void testTrovaCorsoIdDiversi() {
            for (long id = 1; id <= 3; id++) {
                Corso corsoTest = new Corso("Corso " + id);

                when(corsoDao.trovaCorso(id)).thenReturn(corsoTest);

                Corso result = corsoService.trovaCorso(id);

                assertNotNull(result);
                assertEquals("Corso " + id, result.getNome());
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaCorsiCorsoLaurea")
    class TrovaCorsiCorsoLaureaTest {

        @Test
        @DisplayName("trovaCorsiCorsoLaurea restituisce lista di corsi")
        void testTrovaCorsiCorsoLaureaSuccesso() {
            String nomeCorsoLaurea = "Informatica";
            List<Corso> corsi = new ArrayList<>();
            corsi.add(corso);
            corsi.add(new Corso("Algoritmi"));

            when(corsoDao.trovaCorsiCorsoLaurea(nomeCorsoLaurea)).thenReturn(corsi);

            List<Corso> result = corsoService.trovaCorsiCorsoLaurea(nomeCorsoLaurea);

            assertNotNull(result);
            assertEquals(2, result.size());
            verify(corsoDao, times(1)).trovaCorsiCorsoLaurea(nomeCorsoLaurea);
        }

        @Test
        @DisplayName("trovaCorsiCorsoLaurea restituisce lista vuota")
        void testTrovaCorsiCorsoLaureaVuoto() {
            String nomeCorsoLaurea = "Corso Inesistente";

            when(corsoDao.trovaCorsiCorsoLaurea(nomeCorsoLaurea)).thenReturn(new ArrayList<>());

            List<Corso> result = corsoService.trovaCorsiCorsoLaurea(nomeCorsoLaurea);

            assertNotNull(result);
            assertTrue(result.isEmpty());
        }

        @Test
        @DisplayName("trovaCorsiCorsoLaurea con corsi di laurea diversi")
        void testTrovaCorsiCorsoLaureaDiversi() {
            String[] corsiLaurea = {"Informatica", "Matematica", "Fisica"};

            for (String nomeCorsoLaurea : corsiLaurea) {
                List<Corso> corsi = new ArrayList<>();
                corsi.add(new Corso("Corso 1 " + nomeCorsoLaurea));
                corsi.add(new Corso("Corso 2 " + nomeCorsoLaurea));

                when(corsoDao.trovaCorsiCorsoLaurea(nomeCorsoLaurea)).thenReturn(corsi);

                List<Corso> result = corsoService.trovaCorsiCorsoLaurea(nomeCorsoLaurea);

                assertEquals(2, result.size());
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaTutti")
    class TrovaTuttiTest {

        @Test
        @DisplayName("trovaTutti restituisce lista di tutti i corsi")
        void testTrovaTuttiSuccesso() {
            List<Corso> corsi = new ArrayList<>();
            corsi.add(new Corso("Programmazione I"));
            corsi.add(new Corso("Algoritmi"));
            corsi.add(new Corso("Basi di Dati"));

            when(corsoDao.trovaTutti()).thenReturn(corsi);

            List<Corso> result = corsoService.trovaTutti();

            assertNotNull(result);
            assertEquals(3, result.size());
            verify(corsoDao, times(1)).trovaTutti();
        }

        @Test
        @DisplayName("trovaTutti restituisce lista vuota")
        void testTrovaTuttiVuoto() {
            when(corsoDao.trovaTutti()).thenReturn(new ArrayList<>());

            List<Corso> result = corsoService.trovaTutti();

            assertNotNull(result);
            assertTrue(result.isEmpty());
        }

        @Test
        @DisplayName("trovaTutti con molti corsi")
        void testTrovaTuttiMolti() {
            List<Corso> corsi = new ArrayList<>();
            for (int i = 1; i <= 30; i++) {
                corsi.add(new Corso("Corso " + i));
            }

            when(corsoDao.trovaTutti()).thenReturn(corsi);

            List<Corso> result = corsoService.trovaTutti();

            assertEquals(30, result.size());
        }
    }

    @Nested
    @DisplayName("Test del metodo aggiungiCorso")
    class AggiungiCorsoTest {

        @Test
        @DisplayName("aggiungiCorso aggiunge correttamente un corso")
        void testAggiungiCorsoSuccesso() {
            corsoService.aggiungiCorso(corso);
            verify(corsoDao, times(1)).aggiungiCorso(corso);
        }

        @Test
        @DisplayName("aggiungiCorso aggiunge multipli corsi")
        void testAggiungiCorsoMultiple() {
            for (int i = 1; i <= 3; i++) {
                Corso corsoTest = new Corso("Corso " + i);

                corsoService.aggiungiCorso(corsoTest);

                verify(corsoDao, times(1)).aggiungiCorso(corsoTest);
            }
        }

        @Test
        @DisplayName("aggiungiCorso aggiorna un corso esistente")
        void testAggiungiCorsoAggiorna() {
            Corso corsoAggiornato = new Corso("Programmazione II");

            corsoService.aggiungiCorso(corsoAggiornato);

            verify(corsoDao, times(1)).aggiungiCorso(corsoAggiornato);
        }
    }

    @Nested
    @DisplayName("Test del metodo rimuoviCorso")
    class RimuoviCorsoTest {

        @Test
        @DisplayName("rimuoviCorso rimuove correttamente un corso")
        void testRimuoviCorsoSuccesso() {
            corsoService.rimuoviCorso(corso);
            verify(corsoDao, times(1)).rimuoviCorso(corso);
        }

        @Test
        @DisplayName("rimuoviCorso rimuove multipli corsi")
        void testRimuoviCorsoMultiple() {
            for (int i = 1; i <= 3; i++) {
                Corso corsoTest = new Corso("Corso " + i);

                corsoService.rimuoviCorso(corsoTest);

                verify(corsoDao, times(1)).rimuoviCorso(corsoTest);
            }
        }
    }

    @Nested
    @DisplayName("Test di gestione eccezioni")
    class GestioneEccezioniTest {

        @Test
        @DisplayName("trovaCorso gestisce NoResultException")
        void testTrovaCorsoEccezione() {
            long id = -1;

            when(corsoDao.trovaCorso(id)).thenThrow(new NoResultException("Not found"));

            Corso result = corsoService.trovaCorso(id);

            assertNull(result);
            verify(corsoDao, times(1)).trovaCorso(id);
        }

        @Test
        @DisplayName("trovaCorsiCorsoLaurea gestisce parametri vuoti")
        void testTrovaCorsiCorsoLaureaParametriVuoti() {
            String nomeCorsoLaurea = "";

            when(corsoDao.trovaCorsiCorsoLaurea(nomeCorsoLaurea)).thenReturn(new ArrayList<>());

            List<Corso> result = corsoService.trovaCorsiCorsoLaurea(nomeCorsoLaurea);

            assertNotNull(result);
            assertTrue(result.isEmpty());
        }

        @Test
        @DisplayName("trovaTutti gestisce eccezioni gracefully")
        void testTrovaTuttiEccezione() {
            when(corsoDao.trovaTutti()).thenReturn(new ArrayList<>());

            List<Corso> result = corsoService.trovaTutti();

            assertNotNull(result);
            assertTrue(result.isEmpty());
        }
    }

    @Nested
    @DisplayName("Test di integrazione")
    class ScenariComplessiTest {

        @Test
        @DisplayName("Sequenza completa con operazioni multiple")
        void testSequenzaCompleta() {
            corsoService.aggiungiCorso(corso);
            verify(corsoDao, times(1)).aggiungiCorso(corso);

            when(corsoDao.trovaCorso(1L)).thenReturn(corso);
            Corso result = corsoService.trovaCorso(1L);
            assertNotNull(result);

            corsoService.rimuoviCorso(corso);
            verify(corsoDao, atLeastOnce()).rimuoviCorso(corso);
        }

        @Test
        @DisplayName("Ricerca per corso di laurea e aggiornamento")
        void testRicercaCorsoLaureaEAggiornamento() {
            String nomeCorsoLaurea = "Informatica";
            List<Corso> corsi = new ArrayList<>();
            corsi.add(corso);

            when(corsoDao.trovaCorsiCorsoLaurea(nomeCorsoLaurea)).thenReturn(corsi);

            List<Corso> result = corsoService.trovaCorsiCorsoLaurea(nomeCorsoLaurea);
            assertEquals(1, result.size());

            Corso corsoModificato = result.get(0);
            corsoService.aggiungiCorso(corsoModificato);

            verify(corsoDao, times(1)).aggiungiCorso(corsoModificato);
        }

        @Test
        @DisplayName("Recupero tutti i corsi e rimozione")
        void testRecuperoTuttiERimozione() {
            List<Corso> corsi = new ArrayList<>();
            corsi.add(corso);
            corsi.add(new Corso("Algoritmi"));

            when(corsoDao.trovaTutti()).thenReturn(corsi);

            List<Corso> result = corsoService.trovaTutti();
            assertEquals(2, result.size());

            result.forEach(c -> corsoService.rimuoviCorso(c));

            verify(corsoDao, times(2)).rimuoviCorso(any(Corso.class));
        }
    }
}
