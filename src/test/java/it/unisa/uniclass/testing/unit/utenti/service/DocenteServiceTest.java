package it.unisa.uniclass.testing.unit.utenti.service;

import it.unisa.uniclass.common.exceptions.IncorrectUserSpecification;
import it.unisa.uniclass.common.exceptions.NotFoundUserException;
import it.unisa.uniclass.utenti.model.Accademico;
import jakarta.persistence.NoResultException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mock;
import org.mockito.Mockito;
import org.mockito.MockitoAnnotations;

import javax.naming.InitialContext;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class DocenteServiceTest {

    // Sottoclasse per esporre il metodo protected
    static class TestableDocenteService extends DocenteService {
        public TestableDocenteService(DocenteRemote dao) {
            super(dao);
        }
        public AccademicoService exposeAccademicoService() {
            return super.getAccademicoService();
        }
    }

    @Mock
    private DocenteRemote docenteDao;

    @Mock
    private AccademicoService accademicoService;

    private DocenteService docenteService;

    @BeforeEach
    void setUp() {
        MockitoAnnotations.openMocks(this);
        docenteService = new DocenteService(docenteDao);
        docenteService.setAccademicoService(accademicoService); // injection
    }

    @Test
    void testTrovaDocenteUniClass_Esistente() {
        Docente d = new Docente();
        d.setMatricola("123");
        when(docenteDao.trovaDocenteUniClass("123")).thenReturn(d);

        Docente result = docenteService.trovaDocenteUniClass("123");
        assertNotNull(result);
        assertEquals("123", result.getMatricola());
    }

    @Test
    void testTrovaDocenteUniClass_NonTrovato() {
        when(docenteDao.trovaDocenteUniClass("999")).thenThrow(new NoResultException());
        assertNull(docenteService.trovaDocenteUniClass("999"));
    }

    @Test
    void testTrovaEmailUniClass() {
        Docente d = new Docente();
        d.setEmail("a@b.com");
        when(docenteDao.trovaEmailUniClass("a@b.com")).thenReturn(d);
        assertEquals(d, docenteService.trovaEmailUniClass("a@b.com"));
    }

    @Test
    void testTrovaTuttiUniClass() {
        List<Docente> list = Collections.singletonList(new Docente());
        when(docenteDao.trovaTuttiUniClass()).thenReturn(list);
        assertEquals(list, docenteService.trovaTuttiUniClass());
    }

    @Test
    void testTrovaDocenteCorsoLaurea() {
        List<Docente> list = Collections.singletonList(new Docente());
        when(docenteDao.trovaDocenteCorsoLaurea("Ingegneria")).thenReturn(list);
        assertEquals(list, docenteService.trovaDocenteCorsoLaurea("Ingegneria"));
    }

    @Test
    void testAggiungiDocente_Success() throws Exception {
        Docente d = new Docente();
        d.setEmail("a@b.com");
        d.setMatricola("123");
        when(docenteDao.trovaEmailUniClass("a@b.com")).thenReturn(null);
        when(docenteDao.trovaDocenteUniClass("123")).thenReturn(null);

        docenteService.aggiungiDocente(d);
        verify(docenteDao).aggiungiDocente(d);
    }

    @Test
    void testAggiungiDocente_IncorrectUserSpecification() {
        Docente d = new Docente();
        d.setEmail("a@b.com");
        d.setMatricola("123");
        when(docenteDao.trovaEmailUniClass("a@b.com")).thenReturn(new Docente());
        when(docenteDao.trovaDocenteUniClass("123")).thenReturn(new Docente());

        assertThrows(IncorrectUserSpecification.class, () -> docenteService.aggiungiDocente(d));
    }

    @Test
    void testRimuoviDocente_Success() throws Exception {
        Docente d = new Docente();
        d.setMatricola("123");
        Accademico a = new Accademico();

        when(docenteDao.trovaDocenteUniClass("123")).thenReturn(d);
        when(accademicoService.trovaAccademicoUniClass("123")).thenReturn(a);

        docenteService.rimuoviDocente(d);

        verify(docenteDao).rimuoviDocente(d);
        verify(accademicoService).rimuoviAccademico(a);
    }

    @Test
    void testCostruttoreVuoto_JNDIException() {
        RuntimeException ex = assertThrows(RuntimeException.class, () -> new DocenteService());
        assertTrue(ex.getMessage().contains("Errore durante il lookup di DocenteDAO"));
    }

    @Test
    void testTrovaEmailUniClass_NotFound() {
        when(docenteDao.trovaEmailUniClass("missing@b.com")).thenThrow(new NoResultException());
        assertNull(docenteService.trovaEmailUniClass("missing@b.com"));
    }

    @Test
    void testRimuoviDocente_NotFound() {
        Docente d = new Docente();
        d.setMatricola("123");
        when(docenteDao.trovaDocenteUniClass("123")).thenReturn(null);

        assertThrows(NotFoundUserException.class, () -> docenteService.rimuoviDocente(d));
    }

    @Test
    void testCostruttoreDefault_LookupSuccess() throws Exception {
        DocenteRemote fakeDao = mock(DocenteRemote.class);

        try (var mockedCtx = Mockito.mockConstruction(InitialContext.class,
                (mock, context) -> {
                    when(mock.lookup("java:global/UniClass-Dependability/DocenteDAO"))
                            .thenReturn(fakeDao);
                })) {

            DocenteService service = new DocenteService();

            assertNotNull(service); // il costruttore ha eseguito il lookup
        }
    }

    @Test
    void testGetAccademicoService_LazyLoading() {
        DocenteRemote fakeDao = mock(DocenteRemote.class);
        TestableDocenteService service = new TestableDocenteService(fakeDao);

        try (var mockedAcc = Mockito.mockConstruction(AccademicoService.class)) {
            AccademicoService accService = service.exposeAccademicoService();
            assertNotNull(accService); // viene creato un nuovo AccademicoService
        }
    }
}
