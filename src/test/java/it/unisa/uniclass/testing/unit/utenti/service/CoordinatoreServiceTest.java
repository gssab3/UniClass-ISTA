package it.unisa.uniclass.testing.unit.utenti.service;

import it.unisa.uniclass.common.exceptions.AlreadyExistentUserException;
import it.unisa.uniclass.common.exceptions.NotFoundUserException;
import it.unisa.uniclass.utenti.model.Accademico;
import jakarta.persistence.NoResultException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mock;
import org.mockito.MockedConstruction;
import org.mockito.Mockito;
import org.mockito.MockitoAnnotations;

import javax.naming.InitialContext;
import javax.naming.NamingException;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.*;

class CoordinatoreServiceTest {

    @Mock
    private CoordinatoreRemote coordinatoreDao;

    private CoordinatoreService coordinatoreService;

    @BeforeEach
    void setUp() {
        MockitoAnnotations.openMocks(this);
        coordinatoreService = new CoordinatoreService(coordinatoreDao);
    }

    // --- Costruttore di default con JNDI ---
    @Test
    void testCostruttoreDefault() throws Exception {
        try (MockedConstruction<InitialContext> mockedCtx = mockConstruction(InitialContext.class,
                (mock, context) -> {
                    when(mock.lookup("java:global/UniClass-Dependability/CoordinatoreDAO"))
                            .thenReturn(coordinatoreDao);
                })) {
            CoordinatoreService service = new CoordinatoreService();
            assertNotNull(service);
        }
    }

    // --- Trova coordinatore per matricola ---
    @Test
    void testTrovaCoordinatoreUniClass_Esistente() {
        Coordinatore c = new Coordinatore();
        c.setMatricola("0512100001");
        when(coordinatoreDao.trovaCoordinatoreUniClass("0512100001")).thenReturn(c);

        Coordinatore result = coordinatoreService.trovaCoordinatoreUniClass("0512100001");
        assertNotNull(result);
        assertEquals("0512100001", result.getMatricola());
    }

    @Test
    void testTrovaCoordinatoreUniClass_NoResult() {
        when(coordinatoreDao.trovaCoordinatoreUniClass(any())).thenThrow(new NoResultException());
        assertNull(coordinatoreService.trovaCoordinatoreUniClass("fantasma"));
    }

    // --- Trova coordinatore per email ---
    @Test
    void testTrovaCoordinatoreEmailUniclass_Esistente() {
        Coordinatore c = new Coordinatore();
        c.setEmail("coord@unisa.it");
        when(coordinatoreDao.trovaCoordinatoreEmailUniclass("coord@unisa.it")).thenReturn(c);

        Coordinatore result = coordinatoreService.trovaCoordinatoreEmailUniclass("coord@unisa.it");
        assertNotNull(result);
        assertEquals("coord@unisa.it", result.getEmail());
    }

    @Test
    void testTrovaCoordinatoreEmailUniclass_NoResult() {
        when(coordinatoreDao.trovaCoordinatoreEmailUniclass(any())).thenThrow(new NoResultException());
        assertNull(coordinatoreService.trovaCoordinatoreEmailUniclass("fantasma@unisa.it"));
    }

    // --- Trova coordinatori per corso e trova tutti ---
    @Test
    void testTrovaCoordinatoriCorsoLaureaETutti() {
        coordinatoreService.trovaCoordinatoriCorsoLaurea("Ingegneria");
        verify(coordinatoreDao).trovaCoordinatoriCorsoLaurea("Ingegneria");

        coordinatoreService.trovaTutti();
        verify(coordinatoreDao).trovaTutti();
    }

    // --- Aggiungi coordinatore ---
    @Test
    void testAggiungiCoordinatore_Nuovo_Successo() throws Exception {
        Coordinatore c = new Coordinatore();
        c.setMatricola("0512100001");
        c.setEmail("nuovo@unisa.it");

        when(coordinatoreDao.trovaCoordinatoreUniClass(c.getMatricola())).thenReturn(null);
        when(coordinatoreDao.trovaCoordinatoreEmailUniclass(c.getEmail())).thenReturn(null);

        coordinatoreService.aggiungiCoordinatore(c);
        verify(coordinatoreDao).aggiungiCoordinatore(c);
    }

    @Test
    void testAggiungiCoordinatore_Esistente_LanciaEccezione() {
        Coordinatore c = new Coordinatore();
        c.setEmail("esistente@unisa.it");

        when(coordinatoreDao.trovaCoordinatoreEmailUniclass(c.getEmail())).thenReturn(new Coordinatore());

        assertThrows(AlreadyExistentUserException.class, () -> coordinatoreService.aggiungiCoordinatore(c));
        verify(coordinatoreDao, never()).aggiungiCoordinatore(any());
    }

    // --- Rimuovi coordinatore ---
    @Test
    void testRimuoviCoordinatore_Successo() throws Exception {
        Coordinatore c = new Coordinatore();
        c.setMatricola("0512100001");
        c.setEmail("coord@unisa.it");

        when(coordinatoreDao.trovaCoordinatoreEmailUniclass(c.getEmail())).thenReturn(c);

        try (MockedConstruction<AccademicoService> mocked = mockConstruction(AccademicoService.class,
                (mock, context) -> when(mock.trovaAccademicoUniClass(c.getMatricola()))
                        .thenReturn(new Accademico()))) {

            coordinatoreService.rimuoviCoordinatore(c);
            verify(coordinatoreDao).rimuoviCoordinatore(c);
            verify(mocked.constructed().get(0)).rimuoviAccademico(any());
        }
    }

    @Test
    void testRimuoviCoordinatore_NonTrovato() {
        Coordinatore c = new Coordinatore();
        c.setEmail("fantasma@unisa.it");

        when(coordinatoreDao.trovaCoordinatoreEmailUniclass(c.getEmail())).thenReturn(null);

        assertThrows(NotFoundUserException.class, () -> coordinatoreService.rimuoviCoordinatore(c));
        verify(coordinatoreDao, never()).rimuoviCoordinatore(any());
    }

    @Test
    void testCostruttoreDefault_NamingException() {
        try (var mockedCtx = Mockito.mockConstruction(InitialContext.class,
                (mock, context) -> {
                    when(mock.lookup("java:global/UniClass-Dependability/CoordinatoreDAO"))
                            .thenThrow(new NamingException("Simulated JNDI error"));
                })) {

            RuntimeException ex = assertThrows(RuntimeException.class, CoordinatoreService::new);

            assertTrue(ex.getMessage().contains("Errore durante il lookup di CoordinatoreDAO"));
            assertTrue(ex.getCause() instanceof NamingException);
        }
    }
}
